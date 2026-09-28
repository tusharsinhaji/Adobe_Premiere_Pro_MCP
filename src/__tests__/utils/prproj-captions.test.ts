import { gzipSync } from 'zlib';
import { mkdtempSync, writeFileSync, rmSync } from 'fs';
import { tmpdir } from 'os';
import { join } from 'path';
import {
  decodeFormattedText,
  indexProjectXml,
  readSequenceCaptionsFromIndex,
  loadProjectIndex,
  clearProjectIndexCache,
  TICKS_PER_SECOND,
} from '../../utils/prproj-captions.js';
import { PremiereProTools } from '../../tools/index.js';
import { PremiereProBridge } from '../../bridge/index.js';

jest.mock('../../bridge/index.js');

// ---------------------------------------------------------------------------
// A tiny forward-writing FlatBuffer builder, enough to produce caption
// payloads with the field layout the reader expects. Children are written
// after their parents so every uoffset is positive, as the format requires.

type Field =
  | { k: number; f32: number }
  | { k: number; u8: number }
  | { k: number; child: (b: Builder) => number };

class Builder {
  bytes: number[] = [];
  pos(): number { return this.bytes.length; }
  align(n = 4): void { while (this.bytes.length % n) this.bytes.push(0); }
  u8(v: number): void { this.bytes.push(v & 0xff); }
  u16(v: number): void { this.u8(v); this.u8(v >> 8); }
  u32(v: number): void { this.u16(v & 0xffff); this.u16(v >>> 16); }
  f32(v: number): void { const b = Buffer.alloc(4); b.writeFloatLE(v); b.forEach((x) => this.bytes.push(x)); }
  patchU32(at: number, v: number): void {
    this.bytes[at] = v & 0xff; this.bytes[at + 1] = (v >> 8) & 0xff;
    this.bytes[at + 2] = (v >> 16) & 0xff; this.bytes[at + 3] = (v >>> 24) & 0xff;
  }

  table(fields: Field[]): number {
    const wide = fields.filter((f) => !('u8' in f));
    const narrow = fields.filter((f) => 'u8' in f);
    const slots = Math.max(...fields.map((f) => f.k)) + 1;
    const offsets = new Array<number>(slots).fill(0);
    let cursor = 4;
    for (const f of wide) { offsets[f.k] = cursor; cursor += 4; }
    for (const f of narrow) { offsets[f.k] = cursor; cursor += 1; }
    const tableSize = cursor;

    this.align();
    const vt = this.pos();
    this.u16(4 + 2 * slots);
    this.u16(tableSize);
    offsets.forEach((o) => this.u16(o));
    this.align();
    const t = this.pos();
    this.u32(t - vt);
    const pending: Array<{ at: number; child: (b: Builder) => number }> = [];
    for (const f of wide) {
      if ('f32' in f) this.f32(f.f32);
      else { pending.push({ at: this.pos(), child: (f as { child: (b: Builder) => number }).child }); this.u32(0); }
    }
    for (const f of narrow) this.u8((f as { u8: number }).u8);
    for (const p of pending) { const target = p.child(this); this.patchU32(p.at, target - p.at); }
    return t;
  }

  string(s: string): number {
    this.align();
    const at = this.pos();
    const bytes = Buffer.from(s, 'utf8');
    this.u32(bytes.length);
    bytes.forEach((x) => this.u8(x));
    this.u8(0);
    return at;
  }

  vector(children: Array<(b: Builder) => number>): number {
    this.align();
    const at = this.pos();
    this.u32(children.length);
    const slots = children.map(() => { const s = this.pos(); this.u32(0); return s; });
    children.forEach((c, i) => { const target = c(this); this.patchU32(slots[i]!, target - slots[i]!); });
    return at;
  }
}

interface CueSpec { text: string; font: string; size: number; offsetY?: number }

function captionPayload(spec: CueSpec): Buffer {
  const b = new Builder();
  b.u32(0); // root uoffset, patched below
  const docFields: Field[] = [
    { k: 0, child: (x) => x.vector([(y) => y.table([
      { k: 0, child: (z) => z.string(spec.text) },
      { k: 1, child: (z) => z.table([{ k: 1, f32: spec.size }]) },
    ])]) },
    { k: 1, child: (x) => x.vector([(y) => y.string(spec.font)]) },
    { k: 12, f32: 100 },
    { k: 14, f32: 3 },
    { k: 15, f32: 6 },
    { k: 16, f32: 12 },
    { k: 17, child: (x) => x.table([{ k: 0, u8: 0 }, { k: 1, u8: 0 }, { k: 2, u8: 0 }]) },
  ];
  if (spec.offsetY !== undefined) {
    docFields.push({ k: 33, child: (x) => x.table([{ k: 2, f32: spec.offsetY! }]) });
  }
  const root = b.table([{ k: 0, child: (x) => x.table(docFields) }]);
  b.patchU32(0, root);

  const fb = Buffer.from(b.bytes);
  const header = Buffer.alloc(12);
  header.writeUInt32LE(fb.length, 0);
  header.writeUInt32LE(0x11223344, 8);
  return Buffer.concat([header, fb]);
}

// ---------------------------------------------------------------------------
// A minimal project file with one sequence, one visible caption track and one
// hidden caption track.

function projectXml(): string {
  const styled = captionPayload({ text: 'Hello there.', font: 'Arial-BoldMT', size: 72, offsetY: -200 / 1920 }).toString('base64');
  const plain = captionPayload({ text: 'Unstyled cue.', font: 'Monaco', size: 48 }).toString('base64');
  const s = (sec: number) => String(sec * TICKS_PER_SECOND);
  return [
    '<?xml version="1.0" encoding="UTF-8" ?>',
    '<PremiereData Version="3">',
    '\t<Sequence ObjectUID="seq-1" ClassID="x" Version="12">',
    '\t\t<TrackGroups Version="1">',
    '\t\t\t<TrackGroup Version="1" Index="0"><First>video</First><Second ObjectRef="10"/></TrackGroup>',
    '\t\t\t<TrackGroup Version="1" Index="1"><First>data</First><Second ObjectRef="11"/></TrackGroup>',
    '\t\t</TrackGroups>',
    '\t</Sequence>',
    '\t<Sequence ObjectUID="seq-empty" ClassID="x" Version="12">',
    '\t\t<TrackGroups Version="1">',
    '\t\t\t<TrackGroup Version="1" Index="0"><First>video</First><Second ObjectRef="10"/></TrackGroup>',
    '\t\t</TrackGroups>',
    '\t</Sequence>',
    '\t<VideoTrackGroup ObjectID="10" ClassID="x" Version="1">',
    '\t\t<TrackGroup Version="1"><Tracks Version="1"></Tracks></TrackGroup>',
    '\t</VideoTrackGroup>',
    '\t<DataTrackGroup ObjectID="11" ClassID="x" Version="1">',
    '\t\t<TrackGroup Version="1"><Tracks Version="1">',
    '\t\t\t<Track Index="0" ObjectURef="trk-hidden"/>',
    '\t\t\t<Track Index="1" ObjectURef="trk-live"/>',
    '\t\t</Tracks></TrackGroup>',
    '\t</DataTrackGroup>',
    '\t<CaptionDataClipTrack ObjectUID="trk-hidden" ClassID="x" Version="1">',
    '\t\t<DataClipTrack Version="1"><ClipTrack Version="2">',
    '\t\t\t<Track Version="4"><ID>1</ID><IsMuted>true</IsMuted><Index>0</Index></Track>',
    '\t\t\t<ClipItems Version="3"><TrackItems Version="1">',
    '\t\t\t\t<TrackItem Index="0" ObjectRef="22"/>',
    '\t\t\t</TrackItems></ClipItems>',
    '\t\t</ClipTrack></DataClipTrack>',
    '\t</CaptionDataClipTrack>',
    '\t<CaptionDataClipTrack ObjectUID="trk-live" ClassID="x" Version="1">',
    '\t\t<DataClipTrack Version="1"><ClipTrack Version="2">',
    '\t\t\t<Track Version="4"><ID>2</ID><Index>1</Index></Track>',
    '\t\t\t<ClipItems Version="3"><TrackItems Version="1">',
    '\t\t\t\t<TrackItem Index="0" ObjectRef="21"/>',
    '\t\t\t\t<TrackItem Index="1" ObjectRef="20"/>',
    '\t\t\t</TrackItems></ClipItems>',
    '\t\t</ClipTrack></DataClipTrack>',
    '\t</CaptionDataClipTrack>',
    // First cue: Start omitted, which Premiere does when it is 0.
    '\t<CaptionDataClipTrackItem ObjectID="20" ClassID="x" Version="3">',
    `\t\t<TrackItem Version="4"><End>${s(1.5)}</End></TrackItem>`,
    '\t\t<BlockVector Version="1"><BlockVectorItem Index="0" ObjectRef="30"/></BlockVector>',
    '\t</CaptionDataClipTrackItem>',
    '\t<CaptionDataClipTrackItem ObjectID="21" ClassID="x" Version="3">',
    `\t\t<TrackItem Version="4"><Start>${s(1.5)}</Start><End>${s(3)}</End></TrackItem>`,
    '\t\t<BlockVector Version="1"><BlockVectorItem Index="0" ObjectRef="31"/></BlockVector>',
    '\t</CaptionDataClipTrackItem>',
    '\t<CaptionDataClipTrackItem ObjectID="22" ClassID="x" Version="3">',
    `\t\t<TrackItem Version="4"><End>${s(2)}</End></TrackItem>`,
    '\t\t<BlockVector Version="1"><BlockVectorItem Index="0" ObjectRef="32"/></BlockVector>',
    '\t</CaptionDataClipTrackItem>',
    `\t<Block ObjectID="30" ClassID="x" Version="1"><FormattedTextData Encoding="base64" BinaryHash="h-styled">${styled}</FormattedTextData></Block>`,
    // Same payload again: Premiere writes an empty element that reuses the hash.
    '\t<Block ObjectID="31" ClassID="x" Version="1"><FormattedTextData Encoding="base64" BinaryHash="h-styled"/></Block>',
    `\t<Block ObjectID="32" ClassID="x" Version="1"><FormattedTextData Encoding="base64" BinaryHash="h-plain">${plain}</FormattedTextData></Block>`,
    '</PremiereData>',
  ].join('\n');
}

describe('prproj caption reader', () => {
  it('decodes text, font, size, vertical offset and shadow values from a caption payload', () => {
    const decoded = decodeFormattedText(captionPayload({ text: 'Second line.', font: 'Arial-BoldMT', size: 72, offsetY: -200 / 1920 }), 1920);
    expect(decoded).not.toBeNull();
    expect(decoded!.text).toBe('Second line.');
    expect(decoded!.style.font).toBe('Arial-BoldMT');
    expect(decoded!.style.fontSize).toBe(72);
    expect(decoded!.style.offsetYPx).toBe(-200);
    expect(decoded!.style.offsetXFraction).toBe(0);
    expect(decoded!.style.shadow).toEqual({ opacity: 100, distance: 3, size: 6, blur: 12, color: [0, 0, 0] });
  });

  it('returns null rather than throwing on a payload it does not recognise', () => {
    expect(decodeFormattedText(Buffer.from('not a caption payload at all'))).toBeNull();
    const truncated = captionPayload({ text: 'x', font: 'Arial', size: 10 }).subarray(0, 30);
    expect(() => decodeFormattedText(truncated)).not.toThrow();
  });

  it('reads cues in time order, resolves de-duplicated payloads, and reports track visibility', () => {
    const read = readSequenceCaptionsFromIndex(indexProjectXml(projectXml()), 'seq-1', { frameHeight: 1920 });
    expect(read.success).toBe(true);
    expect(read.trackCount).toBe(2);
    expect(read.captionCount).toBe(3);

    const [hidden, live] = read.captionTracks!;
    expect(hidden!.visible).toBe(false);
    expect(hidden!.trackIndex).toBe(0);
    expect(live!.visible).toBe(true);
    expect(live!.trackIndex).toBe(1);

    expect(live!.cues.map((c) => [c.start, c.end, c.text])).toEqual([
      [0, 1.5, 'Hello there.'],
      [1.5, 3, 'Hello there.'],
    ]);
    expect(live!.styles).toEqual([
      { font: 'Arial-BoldMT', fontSize: 72, offsetYPx: -200, offsetYFraction: -0.104167, cueCount: 2 },
    ]);
  });

  it('judges mixed styles only across visible tracks', () => {
    const read = readSequenceCaptionsFromIndex(indexProjectXml(projectXml()), 'seq-1', { frameHeight: 1920 });
    // The hidden track is Monaco 48 and the visible one Arial Bold 72: not mixed on screen.
    expect(read.mixedStyles).toBe(false);
  });

  it('omits per-cue style when asked, but keeps the track summary', () => {
    const read = readSequenceCaptionsFromIndex(indexProjectXml(projectXml()), 'seq-1', { includeStyle: false });
    const cue = read.captionTracks![1]!.cues[0]!;
    expect(cue).not.toHaveProperty('style');
    expect(read.captionTracks![1]!.styles[0]!.font).toBe('Arial-BoldMT');
    expect(read.captionTracks![1]!.styles[0]!.offsetYPx).toBeNull();
  });

  it('reports no caption tracks for a sequence without any', () => {
    const read = readSequenceCaptionsFromIndex(indexProjectXml(projectXml()), 'seq-empty');
    expect(read).toMatchObject({ success: true, trackCount: 0, captionCount: 0, captionTracks: [] });
  });

  it('fails clearly for a sequence that is not in the saved file', () => {
    const read = readSequenceCaptionsFromIndex(indexProjectXml(projectXml()), 'seq-missing');
    expect(read.success).toBe(false);
    expect(read.error).toMatch(/not found in the saved project file/);
  });

  it('reads gzip-compressed and plain project files from disk', async () => {
    const dir = mkdtempSync(join(tmpdir(), 'prproj-captions-'));
    try {
      for (const [name, data] of [['gz.prproj', gzipSync(projectXml())], ['plain.prproj', Buffer.from(projectXml())]] as const) {
        clearProjectIndexCache();
        const path = join(dir, name);
        writeFileSync(path, data);
        const { index } = await loadProjectIndex(path);
        expect(readSequenceCaptionsFromIndex(index, 'seq-1').captionCount).toBe(3);
      }
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });
});

describe('read_sequence_captions tool', () => {
  let dir: string;
  let projectPath: string;
  let tools: PremiereProTools;
  let mockBridge: jest.Mocked<PremiereProBridge>;

  beforeEach(() => {
    dir = mkdtempSync(join(tmpdir(), 'read-captions-tool-'));
    projectPath = join(dir, 'Test.prproj');
    writeFileSync(projectPath, gzipSync(projectXml()));
    clearProjectIndexCache();
    mockBridge = new PremiereProBridge() as jest.Mocked<PremiereProBridge>;
    tools = new PremiereProTools(mockBridge);
  });

  afterEach(() => rmSync(dir, { recursive: true, force: true }));

  it('asks Premiere only for the project path, then reads the captions from that file', async () => {
    mockBridge.executeScript.mockResolvedValue({
      success: true, sequenceId: 'seq-1', sequenceName: 'Reel', projectPath,
      frameWidth: 1080, frameHeight: 1920, savedFirst: false,
    });

    const result: any = await tools.executeTool('read_sequence_captions', {});

    expect(result.success).toBe(true);
    expect(result.captionReadSupported).toBe(true);
    expect(result.source).toBe('saved project file');
    expect(typeof result.projectSavedAt).toBe('string');
    expect(result.captionCount).toBe(3);
    expect(result.captionTracks[1].styles[0]).toMatchObject({ font: 'Arial-BoldMT', fontSize: 72, offsetYPx: -200 });
    const script = mockBridge.executeScript.mock.calls[0]![0] as string;
    expect(script).not.toContain('app.project.save()');
  });

  it('saves first only when saveFirst is true', async () => {
    mockBridge.executeScript.mockResolvedValue({ success: true, sequenceId: 'seq-1', projectPath, frameHeight: 1920, savedFirst: true });

    await tools.executeTool('read_sequence_captions', { saveFirst: true });

    const script = mockBridge.executeScript.mock.calls[0]![0] as string;
    expect(script).toContain('app.project.save()');
  });

  it('refuses to guess when the project has never been saved', async () => {
    mockBridge.executeScript.mockResolvedValue({ success: true, sequenceId: 'seq-1', projectPath: '' });

    const result: any = await tools.executeTool('read_sequence_captions', {});

    expect(result.success).toBe(false);
    expect(result.error).toMatch(/never been saved/);
  });

  it('passes a bridge failure straight through', async () => {
    mockBridge.executeScript.mockResolvedValue({ success: false, error: 'Sequence not found by id: nope' });

    const result: any = await tools.executeTool('read_sequence_captions', { sequenceId: 'nope' });

    expect(result).toEqual({ success: false, error: 'Sequence not found by id: nope' });
  });
});
