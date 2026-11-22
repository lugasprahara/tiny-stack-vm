// tiny-stack-vm: make.fun's tiny stack ISA v1 in one dependency-free
// TypeScript file (Node 22). Per /input/<id> it writes stdout.bin + exit.txt.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const STACK = 256;
const CALLS = 64;
const MEM = 256;
const STEPS = 1000000;
const OUTLIM = 65536;

// Opcode shape: "byte,imm,pops,pushes" per opcode.
const SPEC = "0,0,0,0 1,1,0,1 2,4,0,1 3,0,1,0 4,0,1,2 5,0,2,2 6,0,2,3 7,0,3,3 16,0,2,1 17,0,2,1 18,0,2,1 19,0,2,1 20,0,2,1 21,0,2,1 22,0,2,1 23,0,1,1 24,0,2,1 25,0,2,1 26,0,2,1 27,0,1,1 28,0,2,1 29,0,2,1 30,0,2,1 32,0,2,1 33,0,2,1 34,0,2,1 48,2,0,0 49,2,1,0 50,2,1,0 51,2,0,0 52,0,0,0 64,0,1,1 65,0,2,0 80,0,1,0 81,0,1,0 82,0,0,1 83,0,1,0";
const IMM = new Int8Array(256).fill(-1);
const POPS = new Int8Array(256);
const PUSH = new Int8Array(256);
for (const t of SPEC.split(" ")) {
  const v = t.split(",").map((x) => +x);
  IMM[v[0]] = v[1]; POPS[v[0]] = v[2]; PUSH[v[0]] = v[3];
}

type Outcome = { out: Uint8Array; code: number };

// Runs one program: the bytes it wrote and its exit code (a trap's code).
// Pure: work is budgeted by steps, never the clock.
function run(program: Uint8Array, input: Uint8Array): Outcome {
  const n = program.length;
  const d = new Int32Array(STACK);
  let sp = 0;
  const c = new Int32Array(CALLS);
  let cp = 0;
  const m = new Int32Array(MEM);
  const ob = new Uint8Array(OUTLIM);
  let ol = 0;
  let ip = 0;
  let pc = 0;
  let done = 0;
  const digits = new Uint8Array(11);
  const end = (code: number): Outcome => ({ out: ob.slice(0, ol), code });

  for (;;) {
    if (done === STEPS) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = program[pc];
    const imm = IMM[op];
    if (imm < 0) return end(5);
    if (pc + imm >= n) return end(9);
    done++;
    const next = pc + 1 + imm;
    if (sp < POPS[op]) return end(2);
    if (sp - POPS[op] + PUSH[op] > STACK) return end(3);
    pc = next;

    // Binary ops 0x10-0x22 except NEG/NOT; the division ops share one guard.
    if (op >= 0x10 && op <= 0x22 && op !== 0x17 && op !== 0x1b) {
      const b = d[sp - 1];
      const a = d[sp - 2];
      if (op >= 0x13 && op <= 0x16 && b === 0) return end(4);
      let r = 0;
      switch (op) {
        case 0x10: r = (a + b) | 0; break;
        case 0x11: r = (a - b) | 0; break;
        case 0x12: r = Math.imul(a, b); break;
        case 0x13: r = a === -2147483648 && b === -1 ? a : (a / b) | 0; break;
        case 0x14: r = b === -1 ? 0 : (a % b) | 0; break;
        case 0x15: r = Math.floor((a >>> 0) / (b >>> 0)) | 0; break;
        case 0x16: r = ((a >>> 0) % (b >>> 0)) | 0; break;
        case 0x18: r = a & b; break;
        case 0x19: r = a | b; break;
        case 0x1a: r = a ^ b; break;
        case 0x1c: r = a << (b & 31); break;
        case 0x1d: r = a >> (b & 31); break;
        case 0x1e: r = (a >>> (b & 31)) | 0; break;
        case 0x20: r = a === b ? 1 : 0; break;
        case 0x21: r = a < b ? 1 : 0; break;
        default: r = (a >>> 0) < (b >>> 0) ? 1 : 0;
      }
      sp -= 2;
      d[sp++] = r;
      continue;
    }

    switch (op) {
      case 0x00: return end(0);
      case 0x01: d[sp++] = (program[next - 1] << 24) >> 24; break;
      case 0x02: d[sp++] = program[next - 4] | (program[next - 3] << 8) | (program[next - 2] << 16) | (program[next - 1] << 24); break;
      case 0x03: sp--; break;
      case 0x04: d[sp] = d[sp - 1]; sp++; break;
      case 0x05: { const t = d[sp - 1]; d[sp - 1] = d[sp - 2]; d[sp - 2] = t; break; }
      case 0x06: d[sp] = d[sp - 2]; sp++; break;
      case 0x07: { const a = d[sp - 3]; d[sp - 3] = d[sp - 2]; d[sp - 2] = d[sp - 1]; d[sp - 1] = a; break; }
      case 0x17: d[sp - 1] = -d[sp - 1] | 0; break;
      case 0x1b: d[sp - 1] = ~d[sp - 1]; break;
      case 0x30: case 0x31: case 0x32: {
        const rel = ((program[next - 2] | (program[next - 1] << 8)) << 16) >> 16;
        if (op === 0x30) pc = next + rel;
        else {
          const v = d[--sp];
          if (op === 0x31 ? v === 0 : v !== 0) pc = next + rel;
        }
        break;
      }
      case 0x33:
        if (cp === CALLS) return end(7);
        c[cp++] = next;
        pc = program[next - 2] | (program[next - 1] << 8);
        break;
      case 0x34:
        if (cp === 0) return end(8);
        pc = c[--cp];
        break;
      case 0x40: {
        const addr = d[sp - 1];
        if (addr < 0 || addr >= MEM) return end(6);
        d[sp - 1] = m[addr];
        break;
      }
      case 0x41: {
        const addr = d[sp - 1];
        const v = d[sp - 2];
        if (addr < 0 || addr >= MEM) return end(6);
        sp -= 2;
        m[addr] = v;
        break;
      }
      case 0x50: {
        const v = d[sp - 1];
        let u = v < 0 ? -v : v;
        let k = 0;
        do { digits[k++] = 48 + (u % 10); u = Math.floor(u / 10); } while (u > 0);
        const len = k + (v < 0 ? 1 : 0);
        if (ol + len > OUTLIM) return end(11);
        sp--;
        if (v < 0) ob[ol++] = 45;
        while (k > 0) ob[ol++] = digits[--k];
        break;
      }
      case 0x51:
        if (ol + 1 > OUTLIM) return end(11);
        ob[ol++] = d[--sp] & 255;
        break;
      case 0x52: d[sp++] = ip < input.length ? input[ip++] : -1; break;
      case 0x53: return end(d[--sp] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const program = readFileSync(join(I, id, 'program.bin'));
  const input = readFileSync(join(I, id, 'input.bin'));
  const { out, code } = run(program, input);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), out);
  writeFileSync(join(O, id, 'exit.txt'), code + '\n');
}
