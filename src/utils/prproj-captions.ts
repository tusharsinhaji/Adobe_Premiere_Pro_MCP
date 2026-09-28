/**
 * Read caption tracks out of a saved Premiere Pro project file.
 *
 * Premiere's scripting DOM has no caption read API, but the project file on
 * disk carries every caption cue. A .prproj is gzip-compressed XML. In it:
 *
 *   Sequence (ObjectUID = sequenceID)
 *     TrackGroups -> DataTrackGroup -> Track ObjectURef
 *       CaptionDataClipTrack -> ClipItems/TrackItems -> ObjectRef
 *         CaptionDataClipTrackItem: <Start>/<End> in ticks, BlockVector -> Block
 *           Block: FormattedTextData, a base64 FlatBuffer holding text and style
 *
 * Premiere de-duplicates binary payloads: the first occurrence of a
 * BinaryHash carries the base64 content and later occurrences are empty
 * elements with the same hash, so blobs are resolved through a hash map.
 *
 * The FlatBuffer schema is not published. The field positions below were
 * mapped by decoding cues whose values were read off Premiere's Essential
 * Graphics panel. Only fields checked that way are given names; nothing else
 * in the blob is reported.
 */
import { readFile, stat } from 'fs/promises';
import { gunzipSync } from 'zlib';

export const TICKS_PER_SECOND = 254016000000;

// Offsets into the FormattedTextData FlatBuffer. "doc" is the table the
// root table's field 0 points at.
const DOC_RUNS = 0;             // vector<table>: one entry per text run
const RUN_TEXT = 0;             // string
const RUN_STYLE = 1;            // table
const RUN_STYLE_FONT_SIZE = 1;  // float, points
const RUN_STYLE_FONT_INDEX = 6; // int, index into DOC_FONTS
const DOC_FONTS = 1;            // vector<string>: PostScript font names
const DOC_SHADOW_OPACITY = 12;  // float, 0..100
const DOC_SHADOW_DISTANCE = 14; // float
const DOC_SHADOW_SIZE = 15;     // float
const DOC_SHADOW_BLUR = 16;     // float
const DOC_SHADOW_COLOR = 17;    // table of three u8: r, g, b
const DOC_TRANSFORM = 33;       // table
const TRANSFORM_OFFSET_X = 1;   // float, fraction of frame (only observed at 0)
const TRANSFORM_OFFSET_Y = 2;   // float, fraction of frame height

const FORMATTED_TEXT_MAGIC = 0x11223344;
const FORMATTED_TEXT_HEADER_BYTES = 12; // u64 payload length + u32 magic

export interface CaptionShadow {
  opacity: number | null;
  distance: number | null;
  size: number | null;
  blur: number | null;
  color: [number, number, number] | null;
}

export interface CaptionStyle {
  /** PostScript name, e.g. "Arial-BoldMT". */
  font: string | null;
  fontSize: number | null;
  /** Vertical offset from the caption's default position, as a fraction of frame height. */
  offsetYFraction: number;
  /** offsetYFraction in pixels when the frame height is known. */
  offsetYPx: number | null;
  /** Horizontal offset as stored. Only ever observed at 0, so not converted to pixels. */
  offsetXFraction: number;
  /** Shadow parameter values. Whether the shadow is switched on is not decoded. */
  shadow: CaptionShadow;
}

export interface CaptionCue {
  index: number;
  start: number;
  end: number;
  text: string | null;
  style?: CaptionStyle | null;
  warning?: string;
}

export interface CaptionStyleSummary {
  font: string | null;
  fontSize: number | null;
  offsetYPx: number | null;
  offsetYFraction: number;
  cueCount: number;
}

export interface CaptionTrackRead {
  trackIndex: number;
  trackId: string | null;
  /** False when the track's output is switched off (eye icon), so it does not render. */
  visible: boolean;
  cueCount: number;
  styles: CaptionStyleSummary[];
  cues: CaptionCue[];
}

export interface ProjectCaptionRead {
  success: boolean;
  error?: string;
  trackCount?: number;
  captionCount?: number;
  /** True when the visible caption tracks carry more than one look. Hidden tracks are ignored. */
  mixedStyles?: boolean;
  captionTracks?: CaptionTrackRead[];
}

export interface ReadProjectCaptionsOptions {
  frameHeight?: number | null;
  includeStyle?: boolean;
}

// ---------------------------------------------------------------------------
// XML object index

interface IndexedObject {
  tag: string;
  start: number;
  end: number;
}

interface ProjectIndex {
  xml: string;
  byId: Map<string, IndexedObject>;
  byUid: Map<string, IndexedObject>;
  blobs: Map<string, string>;
}

/**
 * Index the project's top-level objects. Every referenceable object in a
 * .prproj is a direct child of the root element, written one tab in, so a
 * top-level object ends at the next one-tab close tag with the same name.
 */
export function indexProjectXml(xml: string): ProjectIndex {
  const byId = new Map<string, IndexedObject>();
  const byUid = new Map<string, IndexedObject>();
  const open = /\n\t<([A-Za-z0-9_.]+) (ObjectID|ObjectUID)="([^"]+)"/g;
  let match: RegExpExecArray | null;
  while ((match = open.exec(xml)) !== null) {
    const tag = match[1] as string;
    const kind = match[2] as string;
    const key = match[3] as string;
    const start = match.index + 1;
    const openEnd = xml.indexOf('>', start);
    if (openEnd === -1) break;
    let end: number;
    const lineEnd = xml.indexOf('\n', openEnd);
    const inlineClose = xml.indexOf(`</${tag}>`, openEnd);
    if (xml[openEnd - 1] === '/') {
      end = openEnd + 1;
    } else if (inlineClose !== -1 && (lineEnd === -1 || inlineClose < lineEnd)) {
      // Whole object on one line.
      end = inlineClose + tag.length + 3;
    } else {
      // Nested elements are indented deeper, so the object's own close tag is
      // the next one written one tab in.
      const close = xml.indexOf(`\n\t</${tag}>`, start);
      if (close === -1) continue;
      end = close + tag.length + 5;
    }
    const entry: IndexedObject = { tag, start, end };
    if (kind === 'ObjectID') byId.set(key, entry);
    else byUid.set(key, entry);
    open.lastIndex = end;
  }

  const blobs = new Map<string, string>();
  const blob = /Encoding="base64" BinaryHash="([^"]+)">([^<]*)</g;
  while ((match = blob.exec(xml)) !== null) {
    const hash = match[1] as string;
    const content = (match[2] as string).replace(/\s+/g, '');
    if (content && !blobs.has(hash)) blobs.set(hash, content);
  }

  return { xml, byId, byUid, blobs };
}

function body(index: ProjectIndex, obj: IndexedObject | undefined): string | null {
  return obj ? index.xml.slice(obj.start, obj.end) : null;
}

function between(source: string, openTag: string, closeTag: string): string | null {
  const a = source.indexOf(openTag);
  if (a === -1) return null;
  const b = source.indexOf(closeTag, a);
  return b === -1 ? null : source.slice(a, b);
}

// ---------------------------------------------------------------------------
// Minimal FlatBuffer reader. Every read is bounds-checked and returns null
// rather than throwing, because the schema is inferred, not published.

class FlatReader {
  constructor(private readonly b: Buffer) {}

  private fits(o: number, n: number): boolean {
    return Number.isInteger(o) && o >= 0 && o + n <= this.b.length;
  }

  u8(o: number): number | null { return this.fits(o, 1) ? this.b.readUInt8(o) : null; }
  u16(o: number): number | null { return this.fits(o, 2) ? this.b.readUInt16LE(o) : null; }
  i32(o: number): number | null { return this.fits(o, 4) ? this.b.readInt32LE(o) : null; }
  u32(o: number): number | null { return this.fits(o, 4) ? this.b.readUInt32LE(o) : null; }
  f32(o: number): number | null { return this.fits(o, 4) ? this.b.readFloatLE(o) : null; }

  /** Follow the uoffset stored at `o`. */
  deref(o: number): number | null {
    const rel = this.u32(o);
    return rel === null ? null : o + rel;
  }

  /** Absolute position of field `k` in the table at `t`, or null when absent. */
  field(t: number | null, k: number): number | null {
    if (t === null) return null;
    const soff = this.i32(t);
    if (soff === null) return null;
    const vt = t - soff;
    const vsize = this.u16(vt);
    if (vsize === null || vsize < 4) return null;
    const slot = 4 + 2 * k;
    if (slot + 2 > vsize) return null;
    const rel = this.u16(vt + slot);
    return rel ? t + rel : null;
  }

  table(t: number | null, k: number): number | null {
    const pos = this.field(t, k);
    return pos === null ? null : this.deref(pos);
  }

  float(t: number | null, k: number): number | null {
    const pos = this.field(t, k);
    return pos === null ? null : this.f32(pos);
  }

  int(t: number | null, k: number): number | null {
    const pos = this.field(t, k);
    return pos === null ? null : this.i32(pos);
  }

  byte(t: number | null, k: number): number | null {
    const pos = this.field(t, k);
    return pos === null ? null : this.u8(pos);
  }

  stringAt(p: number | null): string | null {
    if (p === null) return null;
    const len = this.u32(p);
    if (len === null || !this.fits(p + 4, len)) return null;
    return this.b.toString('utf8', p + 4, p + 4 + len);
  }

  string(t: number | null, k: number): string | null {
    return this.stringAt(this.table(t, k));
  }

  /** Positions of each element of the vector of offsets in field `k`. */
  vector(t: number | null, k: number): number[] {
    const v = this.table(t, k);
    if (v === null) return [];
    const n = this.u32(v);
    if (n === null || n > 10000) return [];
    const out: number[] = [];
    for (let i = 0; i < n; i++) {
      const e = this.deref(v + 4 + 4 * i);
      if (e !== null) out.push(e);
    }
    return out;
  }
}

function roundTo(value: number | null, places: number): number | null {
  if (value === null || !Number.isFinite(value)) return null;
  const f = 10 ** places;
  return Math.round(value * f) / f;
}

export interface DecodedFormattedText {
  text: string;
  style: CaptionStyle;
}

/** Decode one FormattedTextData payload. Returns null when it is not recognisable. */
export function decodeFormattedText(raw: Buffer, frameHeight?: number | null): DecodedFormattedText | null {
  if (raw.length < FORMATTED_TEXT_HEADER_BYTES + 8) return null;
  if (raw.readUInt32LE(8) !== FORMATTED_TEXT_MAGIC) return null;
  const fb = new FlatReader(raw.subarray(FORMATTED_TEXT_HEADER_BYTES));

  const root = fb.deref(0);
  const doc = fb.table(root, 0);
  if (doc === null) return null;

  const fonts = fb.vector(doc, DOC_FONTS).map((p) => fb.stringAt(p));
  const runs = fb.vector(doc, DOC_RUNS);
  if (runs.length === 0) return null;

  const texts: string[] = [];
  let fontSize: number | null = null;
  let fontIndex: number | null = null;
  runs.forEach((run, i) => {
    texts.push(fb.string(run, RUN_TEXT) ?? '');
    if (i === 0) {
      const style = fb.table(run, RUN_STYLE);
      fontSize = roundTo(fb.float(style, RUN_STYLE_FONT_SIZE), 3);
      fontIndex = fb.int(style, RUN_STYLE_FONT_INDEX) ?? 0;
    }
  });

  const idx = fontIndex ?? 0;
  const font = (idx >= 0 && idx < fonts.length ? fonts[idx] : fonts[0]) ?? null;

  const transform = fb.table(doc, DOC_TRANSFORM);
  const offsetY = transform === null ? 0 : (fb.float(transform, TRANSFORM_OFFSET_Y) ?? 0);
  const offsetX = transform === null ? 0 : (fb.float(transform, TRANSFORM_OFFSET_X) ?? 0);

  const colorTable = fb.table(doc, DOC_SHADOW_COLOR);
  let color: [number, number, number] | null = null;
  if (colorTable !== null) {
    color = [fb.byte(colorTable, 0) ?? 0, fb.byte(colorTable, 1) ?? 0, fb.byte(colorTable, 2) ?? 0];
  }

  return {
    text: texts.join(''),
    style: {
      font,
      fontSize,
      offsetYFraction: roundTo(offsetY, 6) ?? 0,
      offsetYPx: frameHeight ? roundTo(offsetY * frameHeight, 1) : null,
      offsetXFraction: roundTo(offsetX, 6) ?? 0,
      shadow: {
        opacity: roundTo(fb.float(doc, DOC_SHADOW_OPACITY), 3),
        distance: roundTo(fb.float(doc, DOC_SHADOW_DISTANCE), 3),
        size: roundTo(fb.float(doc, DOC_SHADOW_SIZE), 3),
        blur: roundTo(fb.float(doc, DOC_SHADOW_BLUR), 3),
        color,
      },
    },
  };
}

// ---------------------------------------------------------------------------
// Sequence walk

function ticksToSeconds(ticks: string | undefined, fallback: number): number {
  if (ticks === undefined) return fallback;
  return Math.round((Number(ticks) / TICKS_PER_SECOND) * 1e6) / 1e6;
}

export function readSequenceCaptionsFromIndex(
  index: ProjectIndex,
  sequenceId: string,
  options: ReadProjectCaptionsOptions = {},
): ProjectCaptionRead {
  const includeStyle = options.includeStyle !== false;
  const frameHeight = options.frameHeight ?? null;

  const sequence = body(index, index.byUid.get(sequenceId));
  if (!sequence) {
    return { success: false, error: `Sequence ${sequenceId} was not found in the saved project file. If it was created since the last save, save the project first.` };
  }

  const groups = between(sequence, '<TrackGroups', '</TrackGroups>') ?? '';
  const trackUids: string[] = [];
  for (const g of groups.matchAll(/<Second ObjectRef="(\d+)"\/>/g)) {
    const group = index.byId.get(g[1] as string);
    if (!group || group.tag !== 'DataTrackGroup') continue;
    const groupXml = body(index, group) ?? '';
    for (const t of groupXml.matchAll(/<Track Index="\d+" ObjectURef="([^"]+)"\/>/g)) {
      trackUids.push(t[1] as string);
    }
  }

  const tracks: CaptionTrackRead[] = [];
  for (const uid of trackUids) {
    const trackObj = index.byUid.get(uid);
    if (!trackObj || trackObj.tag !== 'CaptionDataClipTrack') continue;
    const trackXml = body(index, trackObj) ?? '';
    const clipItems = between(trackXml, '<ClipItems', '</ClipItems>') ?? '';
    const header = between(trackXml, '<Track Version', '</Track>') ?? '';
    const trackId = /<ID>(\d+)<\/ID>/.exec(header)?.[1] ?? null;
    const trackIndex = Number(/<Index>(\d+)<\/Index>/.exec(header)?.[1] ?? tracks.length);
    const visible = !/<IsMuted>true<\/IsMuted>/.test(header);

    const cues: CaptionCue[] = [];
    for (const item of clipItems.matchAll(/<TrackItem Index="\d+" ObjectRef="(\d+)"\/>/g)) {
      const itemXml = body(index, index.byId.get(item[1] as string));
      if (!itemXml) continue;
      const trackItem = between(itemXml, '<TrackItem Version', '</TrackItem>') ?? itemXml;
      const start = ticksToSeconds(/<Start>(-?\d+)<\/Start>/.exec(trackItem)?.[1], 0);
      const end = ticksToSeconds(/<End>(-?\d+)<\/End>/.exec(trackItem)?.[1], start);

      const texts: string[] = [];
      let style: CaptionStyle | null = null;
      let warning: string | undefined;
      for (const blockRef of itemXml.matchAll(/<BlockVectorItem Index="\d+" ObjectRef="(\d+)"\/>/g)) {
        const blockXml = body(index, index.byId.get(blockRef[1] as string)) ?? '';
        const hash = /FormattedTextData Encoding="base64" BinaryHash="([^"]+)"/.exec(blockXml)?.[1];
        const b64 = hash ? index.blobs.get(hash) : undefined;
        const decoded = b64 ? decodeFormattedText(Buffer.from(b64, 'base64'), frameHeight) : null;
        if (!decoded) {
          warning = 'Caption text payload could not be decoded.';
          continue;
        }
        texts.push(decoded.text);
        if (!style) style = decoded.style;
      }

      const cue: CaptionCue = {
        index: cues.length,
        start,
        end,
        text: texts.length ? texts.join('\n') : null,
        style,
      };
      if (warning) cue.warning = warning;
      cues.push(cue);
    }
    cues.sort((a, b) => a.start - b.start);
    cues.forEach((c, i) => { c.index = i; });
    // Summaries are built from the decoded style before it is dropped from
    // each cue, so they are returned whether or not per-cue style was asked for.
    const styles = summariseStyles(cues);
    if (!includeStyle) cues.forEach((c) => { delete c.style; });

    tracks.push({
      trackIndex,
      trackId,
      visible,
      cueCount: cues.length,
      styles,
      cues,
    });
  }

  tracks.sort((a, b) => a.trackIndex - b.trackIndex);
  const visibleStyles = new Set(tracks.filter((t) => t.visible).flatMap((t) => t.styles.map(styleKey)));
  return {
    success: true,
    trackCount: tracks.length,
    captionCount: tracks.reduce((n, t) => n + t.cueCount, 0),
    mixedStyles: visibleStyles.size > 1,
    captionTracks: tracks,
  };
}

function styleKey(s: { font: string | null; fontSize: number | null; offsetYFraction: number }): string {
  return `${s.font}|${s.fontSize}|${s.offsetYFraction}`;
}

function summariseStyles(cues: CaptionCue[]): CaptionStyleSummary[] {
  const groups = new Map<string, CaptionStyleSummary>();
  for (const cue of cues) {
    if (!cue.style) continue;
    const key = styleKey(cue.style);
    const existing = groups.get(key);
    if (existing) {
      existing.cueCount++;
    } else {
      groups.set(key, {
        font: cue.style.font,
        fontSize: cue.style.fontSize,
        offsetYPx: cue.style.offsetYPx,
        offsetYFraction: cue.style.offsetYFraction,
        cueCount: 1,
      });
    }
  }
  return [...groups.values()].sort((a, b) => b.cueCount - a.cueCount);
}

// ---------------------------------------------------------------------------
// File access, with a one-entry cache keyed on path and modification time so
// repeated reads of an unchanged project do not re-parse tens of megabytes.

let cache: { path: string; mtimeMs: number; index: ProjectIndex } | null = null;

export async function loadProjectIndex(projectPath: string): Promise<{ index: ProjectIndex; savedAt: Date }> {
  const info = await stat(projectPath);
  if (cache && cache.path === projectPath && cache.mtimeMs === info.mtimeMs) {
    return { index: cache.index, savedAt: info.mtime };
  }
  const raw = await readFile(projectPath);
  const isGzip = raw.length > 2 && raw[0] === 0x1f && raw[1] === 0x8b;
  const xml = (isGzip ? gunzipSync(raw) : raw).toString('utf8');
  const index = indexProjectXml(xml);
  cache = { path: projectPath, mtimeMs: info.mtimeMs, index };
  return { index, savedAt: info.mtime };
}

export function clearProjectIndexCache(): void {
  cache = null;
}
