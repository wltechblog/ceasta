#include "core/disasm.h"
#include <capstone/capstone.h>
#include <algorithm>
#include <cstdio>
#include <cstring>

disassembler::~disassembler()
{
    close();
}

void disassembler::close()
{
    if (scratch_) {
        cs_free((cs_insn*)scratch_, 1);
        scratch_ = nullptr;
    }
    if (handle_) {
        csh h = (csh)handle_;
        cs_close(&h);
        handle_ = 0;
    }
}

bool disassembler::open(bin_arch arch)
{
    close();
    csh h = 0;
    cs_err e = arch == bin_arch::mips ? cs_open(CS_ARCH_MIPS, (cs_mode)(CS_MODE_MIPS32 | CS_MODE_LITTLE_ENDIAN), &h)
                                      : arch == bin_arch::arm64 ? cs_open(CS_ARCH_ARM64, CS_MODE_ARM, &h)
                                       : cs_open(CS_ARCH_X86, arch == bin_arch::x64 ? CS_MODE_64 : CS_MODE_32, &h);
    if (e != CS_ERR_OK)
        return false;
    cs_option(h, CS_OPT_DETAIL, CS_OPT_ON);
    scratch_ = cs_malloc(h);
    if (!scratch_) {
        cs_close(&h);
        return false;
    }
    handle_ = (size_t)h;
    arch_ = arch;
    return true;
}

const char* disassembler::reg_name(unsigned reg) const
{
    const char* n = handle_ ? cs_reg_name((csh)handle_, reg) : nullptr;
    return n ? n : "";
}

static bool in_group(const cs_detail* d, uint8_t g)
{
    for (uint8_t i = 0; i < d->groups_count; i++)
        if (d->groups[i] == g)
            return true;
    return false;
}

bool disassembler::decode(const uint8_t* buf, size_t n, uint64_t addr, insn& out)
{
    out = insn();
    if (!handle_ || !buf || n == 0)
        return false;
    if (arch_ == bin_arch::mips)
        return decode_mips(buf, n, addr, out);
    if (arch_ == bin_arch::arm64)
        return decode_arm64(buf, n, addr, out);
    const uint8_t* code = buf;
    size_t size = std::min<size_t>(n, 15); // longest x86 instruction
    uint64_t a = addr;
    cs_insn* ci = (cs_insn*)scratch_;
    if (!cs_disasm_iter((csh)handle_, &code, &size, &a, ci))
        return false;

    out.addr = addr;
    out.size = (uint8_t)ci->size;
    memcpy(out.bytes, ci->bytes, std::min<size_t>(ci->size, sizeof(out.bytes)));
    out.id = ci->id;
    snprintf(out.mnem, sizeof(out.mnem), "%s", ci->mnemonic);
    snprintf(out.ops, sizeof(out.ops), "%s", ci->op_str);

    const cs_detail* d = ci->detail;
    const cs_x86& x = d->x86;
    bool is_jump = in_group(d, CS_GRP_JUMP);
    bool is_call = in_group(d, CS_GRP_CALL);
    bool is_ret = in_group(d, CS_GRP_RET) || in_group(d, CS_GRP_IRET);
    bool far = ci->id == X86_INS_LJMP || ci->id == X86_INS_LCALL;

    if (is_call)
        out.kind = flow::call;
    else if (is_ret)
        out.kind = flow::ret;
    else if (is_jump)
        out.kind = (ci->id == X86_INS_JMP || ci->id == X86_INS_LJMP) ? flow::jump : flow::cond;
    else if (ci->id == X86_INS_HLT || ci->id == X86_INS_UD2 || ci->id == X86_INS_UD1 || ci->id == X86_INS_UD0 || ci->id == X86_INS_INT3)
        out.kind = flow::stop;
    else if (ci->id == X86_INS_INT && x.op_count == 1 && x.operands[0].type == X86_OP_IMM && x.operands[0].imm == 0x29)
        out.kind = flow::stop; // __fastfail
    out.is_lea = ci->id == X86_INS_LEA;

    bool branch = is_jump || is_call;
    uint64_t mask = arch_ == bin_arch::x64 ? ~0ull : 0xffffffffull;
    int regs_seen = 0;
    for (uint8_t i = 0; i < x.op_count && i < 8; i++) {
        const cs_x86_op& op = x.operands[i];
        if (op.type == X86_OP_IMM) {
            if (branch && !far) {
                out.has_target = true;
                out.target = (uint64_t)op.imm & mask;
            } else if (!out.has_imm) {
                out.has_imm = true;
                out.imm = (uint64_t)op.imm & mask;
            }
        } else if (op.type == X86_OP_REG) {
            if (branch)
                out.indirect = true;
            if (regs_seen == 0)
                out.reg0 = op.reg;
            else if (regs_seen == 1)
                out.reg1 = op.reg;
            regs_seen++;
        } else if (op.type == X86_OP_MEM) {
            if (branch)
                out.indirect = true;
            out.has_mem_op = true;
            out.mem_base = op.mem.base;
            out.mem_index = op.mem.index;
            out.mem_scale = op.mem.scale;
            out.mem_disp = op.mem.disp;
            out.mem_size = op.size;
            out.mem_write = (op.access & CS_AC_WRITE) != 0;
            bool seg_rel = op.mem.segment == X86_REG_FS || op.mem.segment == X86_REG_GS;
            if (op.mem.base == X86_REG_RIP && op.mem.index == X86_REG_INVALID) {
                out.has_mem = true;
                out.mem_rip = true;
                out.mem = addr + ci->size + (uint64_t)op.mem.disp;
            } else if (op.mem.base == X86_REG_EIP && op.mem.index == X86_REG_INVALID) {
                out.has_mem = true;
                out.mem_rip = true;
                out.mem = (addr + ci->size + (uint64_t)op.mem.disp) & 0xffffffffull;
            } else if (op.mem.base == X86_REG_INVALID && op.mem.index == X86_REG_INVALID && !seg_rel) {
                out.has_mem = true;
                out.mem = (uint64_t)op.mem.disp & mask;
            }
        }
    }
    if (far)
        out.indirect = true;
    if (out.indirect)
        out.has_target = false;
    return true;
}

// ---- arm64 ----

namespace {

// bytes a register holds, by its name: w 4, x 8, b 1, h 2, s 4, d 8, q and v 16
unsigned a64_reg_bytes(const char* n)
{
    if (!n || !*n)
        return 0;
    if (!strcmp(n, "sp") || !strcmp(n, "fp") || !strcmp(n, "lr") || !strcmp(n, "xzr"))
        return 8;
    if (!strcmp(n, "wsp") || !strcmp(n, "wzr"))
        return 4;
    switch (n[0]) {
    case 'w': return 4;
    case 'x': return 8;
    case 'b': return 1;
    case 'h': return 2;
    case 's': return 4;
    case 'd': return 8;
    case 'q': case 'v': case 'z': return 16;
    default: return 0;
    }
}

bool starts(const char* s, const char* p)
{
    return strncmp(s, p, strlen(p)) == 0;
}

// loads and stores: ld*, st* and the atomics that read and write memory
bool a64_mem_insn(const char* m)
{
    return (m[0] == 'l' && m[1] == 'd') || (m[0] == 's' && m[1] == 't') || starts(m, "cas") || starts(m, "swp");
}

// the flag setting aliases that name a register they only read (cmp is subs wzr, ...)
bool a64_no_dest(const char* m)
{
    return !strcmp(m, "cmp") || !strcmp(m, "cmn") || !strcmp(m, "tst") || !strcmp(m, "ccmp") || !strcmp(m, "ccmn") ||
           starts(m, "fcmp") || starts(m, "fccmp");
}

} // namespace

bool disassembler::decode_arm64(const uint8_t* buf, size_t n, uint64_t addr, insn& out)
{
    if (n < 4 || (addr & 3))
        return false;
    const uint8_t* code = buf;
    size_t size = 4;
    uint64_t a = addr;
    cs_insn* ci = (cs_insn*)scratch_;
    if (!cs_disasm_iter((csh)handle_, &code, &size, &a, ci))
        return false;
    csh h = (csh)handle_;
    out.arm = true;
    out.addr = addr;
    out.size = 4;
    memcpy(out.bytes, ci->bytes, 4);
    out.id = ci->id;
    snprintf(out.mnem, sizeof(out.mnem), "%s", ci->mnemonic);
    snprintf(out.ops, sizeof(out.ops), "%s", ci->op_str);
    const cs_arm64& x = ci->detail->arm64;
    unsigned id = ci->id;
    out.sets_flags = x.update_flags;

    switch (id) {
    case ARM64_INS_BL: case ARM64_INS_BLR: case ARM64_INS_BLRAA: case ARM64_INS_BLRAAZ: case ARM64_INS_BLRAB:
    case ARM64_INS_BLRABZ:
        out.kind = flow::call;
        out.indirect = id != ARM64_INS_BL;
        break;
    case ARM64_INS_B:
        out.kind = x.cc == ARM64_CC_INVALID || x.cc == ARM64_CC_AL || x.cc == ARM64_CC_NV ? flow::jump : flow::cond;
        break;
    case ARM64_INS_BR: case ARM64_INS_BRAA: case ARM64_INS_BRAAZ: case ARM64_INS_BRAB: case ARM64_INS_BRABZ:
        out.kind = flow::jump;
        out.indirect = true;
        break;
    case ARM64_INS_CBZ: case ARM64_INS_CBNZ: case ARM64_INS_TBZ: case ARM64_INS_TBNZ:
        out.kind = flow::cond;
        break;
    case ARM64_INS_RET: case ARM64_INS_RETAA: case ARM64_INS_RETAB: case ARM64_INS_ERET: case ARM64_INS_ERETAA:
    case ARM64_INS_ERETAB:
        out.kind = flow::ret;
        break;
    case ARM64_INS_BRK: case ARM64_INS_HLT: case ARM64_INS_UDF:
        out.kind = flow::stop;
        break;
    default:
        break;
    }
    bool branch = out.kind == flow::jump || out.kind == flow::cond || out.kind == flow::call;
    const char* m = ci->mnemonic;
    bool mem_insn = a64_mem_insn(m);
    bool store = mem_insn && (m[0] == 's' || starts(m, "cas") || starts(m, "swp"));
    size_t ml = strlen(m);
    char last = ml ? m[ml - 1] : 0;
    // ldp, stp, ldnp, ldxp, stlxp, ldpsw ... (swp is a swap, not a pair)
    bool pair = mem_insn && !starts(m, "swp") && (last == 'p' || starts(m, "ldpsw"));
    unsigned access = 0; // bytes one register of the load / store moves
    if (mem_insn) {
        if (strstr(m, "sw"))
            access = 4;
        else if (last == 'b' && !starts(m, "st1") && !starts(m, "ld1"))
            access = 1;
        else if (last == 'h')
            access = 2;
        out.mem_signed = strstr(m + 2, "rs") != nullptr || starts(m, "ldpsw");
    }

    auto add_write = [&](unsigned reg) {
        int r = regs::a64_num(reg);
        if (r < 0 || out.nwr >= 3)
            return;
        for (uint8_t i = 0; i < out.nwr; i++)
            if (out.wr[i] == (uint8_t)r)
                return;
        out.wr[out.nwr++] = (uint8_t)r;
    };
    bool no_dest = a64_no_dest(m);
    int regs_seen = 0;
    bool literal = false;
    for (uint8_t i = 0; i < x.op_count && i < 8; i++) {
        const cs_arm64_op& op = x.operands[i];
        if (op.type == ARM64_OP_REG) {
            if (regs_seen == 0)
                out.reg0 = op.reg;
            else if (regs_seen == 1)
                out.reg1 = op.reg;
            else if (regs_seen == 2)
                out.reg2 = op.reg;
            regs_seen++;
            if ((op.access & CS_AC_WRITE) && !no_dest && !store)
                add_write(op.reg);
            if (op.ext || op.shift.type == ARM64_SFT_LSL) {
                out.ext = op.ext ? (uint8_t)(a64_uxtb + (op.ext - ARM64_EXT_UXTB)) : (uint8_t)a64_lsl;
                out.shift = (uint8_t)op.shift.value;
            }
            if (mem_insn && !access && regs_seen == 1)
                access = a64_reg_bytes(cs_reg_name(h, op.reg));
        } else if (op.type == ARM64_OP_IMM) {
            if (branch) {
                out.has_target = true; // the last one: tbz w0, #3, target
                out.target = (uint64_t)op.imm;
            } else if (id == ARM64_INS_ADRP) {
                out.has_page = true;
                out.page = (uint64_t)op.imm;
            } else if (id == ARM64_INS_ADR) {
                out.has_mem = true;
                out.is_lea = true;
                out.mem = (uint64_t)op.imm;
            } else if (mem_insn && regs_seen >= 1 && !x.post_index && i == regs_seen) {
                literal = true; // ldr x0, #address
                out.has_mem = true;
                out.mem = (uint64_t)op.imm;
            } else if (!out.has_imm) {
                out.has_imm = true;
                uint64_t v = (uint64_t)op.imm;
                if (op.shift.type == ARM64_SFT_LSL && op.shift.value < 64)
                    v <<= op.shift.value;
                out.imm = v;
            }
        } else if (op.type == ARM64_OP_MEM) {
            out.has_mem_op = true;
            out.mem_base = op.mem.base;
            out.mem_index = op.mem.index;
            out.mem_disp = op.mem.disp;
            out.mem_scale = op.mem.index ? 1 << (op.shift.type == ARM64_SFT_LSL ? op.shift.value : 0) : 0;
            out.mem_write = store;
            if (x.writeback)
                add_write(op.mem.base);
        }
    }
    if (mem_insn && !starts(m, "prfm")) {
        out.mem_size = (uint8_t)std::min(access * (pair ? 2 : 1), 255u);
        if (literal)
            out.mem_write = false;
    } else if (starts(m, "prfm")) {
        out.has_mem = false; // a prefetch touches nothing
        out.has_mem_op = false;
    }
    if (out.kind == flow::call)
        add_write(ARM64_REG_LR);
    if (out.indirect)
        out.has_target = false;
    return true;
}

// ---- mips32 (little endian) ----

namespace {

// bytes a load or store of this instruction moves, 0 when it touches no memory
unsigned mips_mem_size(unsigned id)
{
    switch (id) {
    case MIPS_INS_LB: case MIPS_INS_LBU: case MIPS_INS_SB:
        return 1;
    case MIPS_INS_LH: case MIPS_INS_LHU: case MIPS_INS_SH:
        return 2;
    case MIPS_INS_LW: case MIPS_INS_SW: case MIPS_INS_LWL: case MIPS_INS_LWR:
    case MIPS_INS_LWC1: case MIPS_INS_SWC1: case MIPS_INS_LL: case MIPS_INS_SC:
        return 4;
    case MIPS_INS_LDC1: case MIPS_INS_SDC1:
        return 8;
    default:
        return 0;
    }
}

bool mips_is_store(unsigned id)
{
    switch (id) {
    case MIPS_INS_SB: case MIPS_INS_SH: case MIPS_INS_SW: case MIPS_INS_SWL: case MIPS_INS_SWR:
    case MIPS_INS_SC: case MIPS_INS_SWC1: case MIPS_INS_SDC1:
        return true;
    default:
        return false;
    }
}

} // namespace

bool disassembler::decode_mips(const uint8_t* buf, size_t n, uint64_t addr, insn& out)
{
    if (n < 4 || (addr & 3))
        return false;
    const uint8_t* code = buf;
    size_t size = 4;
    uint64_t a = addr;
    cs_insn* ci = (cs_insn*)scratch_;
    if (!cs_disasm_iter((csh)handle_, &code, &size, &a, ci))
        return false;
    out.mips = true;
    out.addr = addr;
    out.size = 4;
    memcpy(out.bytes, ci->bytes, 4);
    out.id = ci->id;
    snprintf(out.mnem, sizeof(out.mnem), "%s", ci->mnemonic);
    snprintf(out.ops, sizeof(out.ops), "%s", ci->op_str);
    const cs_mips& x = ci->detail->mips;
    unsigned id = ci->id;

    bool store = mips_is_store(id);
    bool links = false; // writes ra whatever the branch does (bal, bltzal / bgezal)
    switch (id) {
    case MIPS_INS_BAL: case MIPS_INS_BLTZAL: case MIPS_INS_BGEZAL:
    case MIPS_INS_BLTZALL: case MIPS_INS_BGEZALL:
        // bal is bgezal $zero; a real bltzal / bgezal branches conditionally
        out.kind = id == MIPS_INS_BAL || (x.op_count && x.operands[0].type == MIPS_OP_REG &&
                                          x.operands[0].reg == MIPS_REG_ZERO)
                       ? flow::call
                       : flow::cond;
        links = true;
        break;
    case MIPS_INS_JAL:
        out.kind = flow::call;
        links = true;
        break;
    case MIPS_INS_JALR:
        out.kind = flow::call;
        out.indirect = true;
        break;
    case MIPS_INS_JR:
        // jr $ra ends a function
        out.kind = x.op_count == 1 && x.operands[0].type == MIPS_OP_REG && x.operands[0].reg == MIPS_REG_RA
                       ? flow::ret
                       : flow::jump;
        out.indirect = true;
        break;
    case MIPS_INS_J: case MIPS_INS_B:
        out.kind = flow::jump;
        break;
    case MIPS_INS_BEQ: case MIPS_INS_BNE: case MIPS_INS_BLEZ: case MIPS_INS_BGTZ:
    case MIPS_INS_BLTZ: case MIPS_INS_BGEZ: case MIPS_INS_BEQL: case MIPS_INS_BNEL:
    case MIPS_INS_BLEZL: case MIPS_INS_BGTZL: case MIPS_INS_BLTZL: case MIPS_INS_BGEZL:
        out.kind = flow::cond;
        break;
    case MIPS_INS_BREAK: case MIPS_INS_SDBBP: case MIPS_INS_SDBBP16:
        out.kind = flow::stop; // traps nobody comes back from in normal flow
        break;
    case MIPS_INS_WAIT: case MIPS_INS_ERET: case MIPS_INS_DERET:
        out.kind = flow::stop;
        break;
    default:
        break;
    }
    bool branch = out.kind == flow::jump || out.kind == flow::cond ||
                  (out.kind == flow::call && id != MIPS_INS_JALR);

    int regs_seen = 0;
    for (uint8_t i = 0; i < x.op_count && i < 8; i++) {
        const cs_mips_op& op = x.operands[i];
        if (op.type == MIPS_OP_REG) {
            if (regs_seen == 0)
                out.reg0 = op.reg;
            else if (regs_seen == 1)
                out.reg1 = op.reg;
            else if (regs_seen == 2)
                out.reg2 = op.reg;
            regs_seen++;
        } else if (op.type == MIPS_OP_IMM) {
            if (branch && id != MIPS_INS_JALR) {
                out.has_target = true;
                out.target = (uint64_t)op.imm & 0xffffffffull;
            } else if (!out.has_imm) {
                out.has_imm = true;
                // lui's immediate is the high half of the constant the pair builds
                out.imm = ((uint64_t)op.imm << (id == MIPS_INS_LUI ? 16 : 0)) & 0xffffffffull;
            }
        } else if (op.type == MIPS_OP_MEM) {
            out.has_mem_op = true;
            out.mem_base = op.mem.base;
            out.mem_index = 0;
            out.mem_scale = 0;
            out.mem_disp = (int64_t)op.mem.disp;
            out.mem_write = store;
        }
    }
    unsigned msz = mips_mem_size(id);
    if (out.has_mem_op && msz) {
        out.mem_size = (uint8_t)msz;
        if (!store) {
            out.mem_write = false;
            // lb, lh, lwl sign extend
            out.mem_signed = id == MIPS_INS_LB || id == MIPS_INS_LH || id == MIPS_INS_LWL;
        }
    } else if (out.has_mem_op) {
        out.has_mem_op = false; // a memory operand we know nothing about
        out.mem_base = 0;
        out.mem_disp = 0;
    }
    // what it writes: the first register operand, when that's a destination (jal / bal write ra)
    if (!branch && !store && x.op_count && x.operands[0].type == MIPS_OP_REG) {
        int r = regs::mips_num(x.operands[0].reg);
        if (r >= 0 && out.nwr < 3)
            out.wr[out.nwr++] = (uint8_t)r;
    }
    if (links && id != MIPS_INS_JALR && out.nwr < 3)
        out.wr[out.nwr++] = (uint8_t)regs::mips_num(MIPS_REG_RA);
    if (out.indirect)
        out.has_target = false;
    return true;
}

bool disassembler::decode(const binary& b, uint64_t addr, insn& out)
{
    uint8_t buf[16];
    size_t n = b.read(addr, buf, sizeof(buf));
    if (n == 0) {
        out = insn();
        return false;
    }
    return decode(buf, n, addr, out);
}

namespace regs {

unsigned rip() { return X86_REG_RIP; }
unsigned eip() { return X86_REG_EIP; }
unsigned ebx() { return X86_REG_EBX; }

static unsigned canon(unsigned r)
{
    switch (r) {
    case X86_REG_AL: case X86_REG_AH: case X86_REG_AX: case X86_REG_EAX: case X86_REG_RAX: return X86_REG_RAX;
    case X86_REG_BL: case X86_REG_BH: case X86_REG_BX: case X86_REG_EBX: case X86_REG_RBX: return X86_REG_RBX;
    case X86_REG_CL: case X86_REG_CH: case X86_REG_CX: case X86_REG_ECX: case X86_REG_RCX: return X86_REG_RCX;
    case X86_REG_DL: case X86_REG_DH: case X86_REG_DX: case X86_REG_EDX: case X86_REG_RDX: return X86_REG_RDX;
    case X86_REG_SIL: case X86_REG_SI: case X86_REG_ESI: case X86_REG_RSI: return X86_REG_RSI;
    case X86_REG_DIL: case X86_REG_DI: case X86_REG_EDI: case X86_REG_RDI: return X86_REG_RDI;
    case X86_REG_BPL: case X86_REG_BP: case X86_REG_EBP: case X86_REG_RBP: return X86_REG_RBP;
    case X86_REG_SPL: case X86_REG_SP: case X86_REG_ESP: case X86_REG_RSP: return X86_REG_RSP;
    case X86_REG_R8B: case X86_REG_R8W: case X86_REG_R8D: case X86_REG_R8: return X86_REG_R8;
    case X86_REG_R9B: case X86_REG_R9W: case X86_REG_R9D: case X86_REG_R9: return X86_REG_R9;
    case X86_REG_R10B: case X86_REG_R10W: case X86_REG_R10D: case X86_REG_R10: return X86_REG_R10;
    case X86_REG_R11B: case X86_REG_R11W: case X86_REG_R11D: case X86_REG_R11: return X86_REG_R11;
    case X86_REG_R12B: case X86_REG_R12W: case X86_REG_R12D: case X86_REG_R12: return X86_REG_R12;
    case X86_REG_R13B: case X86_REG_R13W: case X86_REG_R13D: case X86_REG_R13: return X86_REG_R13;
    case X86_REG_R14B: case X86_REG_R14W: case X86_REG_R14D: case X86_REG_R14: return X86_REG_R14;
    case X86_REG_R15B: case X86_REG_R15W: case X86_REG_R15D: case X86_REG_R15: return X86_REG_R15;
    default: return r;
    }
}

bool same_reg(unsigned a, unsigned b)
{
    return a != X86_REG_INVALID && canon(a) == canon(b);
}

int a64_num(unsigned r)
{
    if (r >= ARM64_REG_X0 && r <= ARM64_REG_X28)
        return (int)(r - ARM64_REG_X0);
    if (r >= ARM64_REG_W0 && r <= ARM64_REG_W30)
        return (int)(r - ARM64_REG_W0);
    switch (r) {
    case ARM64_REG_FP: return 29;
    case ARM64_REG_LR: return 30;
    case ARM64_REG_SP: case ARM64_REG_WSP: return 31;
    default: return -1;
    }
}

int mips_num(unsigned r)
{
    if (r >= MIPS_REG_0 && r <= MIPS_REG_31)
        return (int)(r - MIPS_REG_0);
    return -1;
}

}

namespace ins {

bool is_nop(const insn& in)
{
    return in.mips ? in.id == MIPS_INS_NOP : in.arm ? in.id == ARM64_INS_NOP : in.id == X86_INS_NOP;
}
bool is_endbr(const insn& in)
{
    return in.mips ? false : in.arm ? in.id == ARM64_INS_BTI : in.id == X86_INS_ENDBR64 || in.id == X86_INS_ENDBR32;
}
bool is_movsxd(const insn& in) { return !in.arm && in.id == X86_INS_MOVSXD; }
bool is_move(const insn& in)
{
    return !in.arm && (in.id == X86_INS_MOV || in.id == X86_INS_MOVSXD || in.id == X86_INS_MOVZX || in.id == X86_INS_MOVSX);
}
bool is_add(const insn& in) { return !in.arm && in.id == X86_INS_ADD; }
bool is_cmp(const insn& in) { return !in.arm && in.id == X86_INS_CMP; }
bool is_ja(const insn& in) { return !in.arm && in.id == X86_INS_JA; }
bool is_jae(const insn& in) { return !in.arm && in.id == X86_INS_JAE; }
bool is_push(const insn& in) { return !in.arm && in.id == X86_INS_PUSH; }

bool is_suspicious(const insn& in)
{
    if (in.mips) {
        switch (in.id) {
        case MIPS_INS_MFC0: case MIPS_INS_MTC0: case MIPS_INS_ERET: case MIPS_INS_DERET:
        case MIPS_INS_WAIT: case MIPS_INS_DI: case MIPS_INS_EI: case MIPS_INS_CACHE:
        case MIPS_INS_SDBBP: case MIPS_INS_BREAK:
            return true;
        default:
            return false;
        }
    }
    if (in.arm) {
        switch (in.id) {
        case ARM64_INS_HVC: case ARM64_INS_SMC: case ARM64_INS_ERET: case ARM64_INS_ERETAA: case ARM64_INS_ERETAB:
        case ARM64_INS_DCPS1: case ARM64_INS_DCPS2: case ARM64_INS_DCPS3: case ARM64_INS_HLT:
            return true;
        default:
            return false;
        }
    }
    switch (in.id) {
    case X86_INS_IN: case X86_INS_OUT: case X86_INS_INSB: case X86_INS_INSD: case X86_INS_INSW:
    case X86_INS_OUTSB: case X86_INS_OUTSD: case X86_INS_OUTSW: case X86_INS_CLI: case X86_INS_STI:
    case X86_INS_HLT: case X86_INS_IRET: case X86_INS_IRETD: case X86_INS_IRETQ: case X86_INS_LJMP:
    case X86_INS_LCALL: case X86_INS_RETF: case X86_INS_INTO: case X86_INS_BOUND: case X86_INS_ARPL:
    case X86_INS_AAA: case X86_INS_AAD: case X86_INS_AAM: case X86_INS_AAS: case X86_INS_DAA:
    case X86_INS_DAS: case X86_INS_LES: case X86_INS_LDS: case X86_INS_SALC: case X86_INS_INT1:
    case X86_INS_SYSEXIT: case X86_INS_SYSRET:
        return true;
    default:
        return false;
    }
}

bool a64_adrp(const insn& in) { return in.arm && in.has_page; }
bool a64_add_imm(const insn& in) { return in.arm && in.id == ARM64_INS_ADD && in.has_imm && in.reg0 && in.reg1 && !in.reg2; }
bool a64_add_reg(const insn& in) { return in.arm && in.id == ARM64_INS_ADD && !in.has_imm && in.reg2; }
bool a64_mov_reg(const insn& in) { return in.arm && in.id == ARM64_INS_MOV && !in.has_imm && in.reg0 && in.reg1 && !in.reg2; }
bool a64_cmp_imm(const insn& in) { return in.arm && in.id == ARM64_INS_CMP && in.has_imm && in.reg0; }
bool a64_bhi(const insn& in) { return in.arm && in.kind == flow::cond && !strcmp(in.mnem, "b.hi"); }
bool a64_bhs(const insn& in) { return in.arm && in.kind == flow::cond && (!strcmp(in.mnem, "b.hs") || !strcmp(in.mnem, "b.cs")); }
bool a64_bls(const insn& in) { return in.arm && in.kind == flow::cond && !strcmp(in.mnem, "b.ls"); }
bool a64_blo(const insn& in) { return in.arm && in.kind == flow::cond && (!strcmp(in.mnem, "b.lo") || !strcmp(in.mnem, "b.cc")); }

bool a64_prologue(uint32_t w)
{
    return ((w & 0xffc07fff) == 0xa9807bfd && (w & 0x00200000)) || // stp x29, x30, [sp, #-n]!
           (w & 0xff8003ff) == 0xd10003ff ||                        // sub sp, sp, #n
           w == 0xd503233f || w == 0xd503237f ||                    // paciasp, pacibsp
           w == 0xd503245f || w == 0xd50324df;                      // bti c, bti jc
}

bool a64_gap_before(uint32_t w)
{
    return w == 0 || w == 0xd65f03c0 || w == 0xd65f0bff || w == 0xd65f0fff || // udf, ret, retaa, retab
           w == 0xd503201f ||                                               // nop
           (w & 0xfc000000) == 0x14000000 ||                                // b
           (w & 0xfffffc1f) == 0xd61f0000 ||                                // br
           (w & 0xffe0001f) == 0xd4200000;                                  // brk
}

bool mips_prologue(uint32_t w)
{
    unsigned op = w >> 26, rs = (w >> 21) & 31, rt = (w >> 16) & 31;
    return (op == 9 && rs == 29 && rt == 29) ||   // addiu sp, sp, n
           (op == 0x2b && rs == 29 && rt == 31);  // sw ra, n(sp)
}

// mips instruction classes the analysis tracks registers over
bool mips_lui(const insn& in) { return in.mips && in.id == MIPS_INS_LUI && in.has_imm; }
bool mips_addiu(const insn& in)
{
    return in.mips && (in.id == MIPS_INS_ADDIU || in.id == MIPS_INS_ADDI) && in.has_imm;
}
bool mips_ori(const insn& in) { return in.mips && in.id == MIPS_INS_ORI && in.has_imm; }
bool mips_xori(const insn& in) { return in.mips && in.id == MIPS_INS_XORI && in.has_imm; }
bool mips_andi(const insn& in) { return in.mips && in.id == MIPS_INS_ANDI && in.has_imm; }
bool mips_addu(const insn& in) { return in.mips && (in.id == MIPS_INS_ADDU || in.id == MIPS_INS_ADD); }
bool mips_subu(const insn& in) { return in.mips && (in.id == MIPS_INS_SUBU || in.id == MIPS_INS_SUB); }
bool mips_move(const insn& in) { return in.mips && in.id == MIPS_INS_MOVE; }
bool mips_lw(const insn& in) { return in.mips && in.id == MIPS_INS_LW; }
bool mips_slti(const insn& in)
{
    return in.mips && (in.id == MIPS_INS_SLTI || in.id == MIPS_INS_SLTIU) && in.has_imm;
}
bool mips_sll(const insn& in) { return in.mips && in.id == MIPS_INS_SLL && in.has_imm; }
bool mips_sllv(const insn& in) { return in.mips && in.id == MIPS_INS_SLLV; }

bool mips_gap_before(uint32_t w)
{
    if (w == 0)
        return true;                                 // nop, or zero padding
    unsigned op = w >> 26, rs = (w >> 21) & 31, fn = w & 0x3f;
    return (op == 0 && rs == 31 && fn == 8) ||       // jr ra
           (op == 4 && rs == 0 && ((w >> 16) & 31) == 0) || // b offset
           (op == 0 && fn == 0x0d) ||               // break
           (op == 0x1f && (w & 0x3f) == 0x3f);      // sdbbp
}

}

// ---- what an instruction writes (for undoing steps) ----

namespace {

// the full register a sub-register lives in, named the way the debugger names it
const char* full_reg_name(unsigned r, bool x64)
{
    if (r == X86_REG_EIP || r == X86_REG_IP || r == X86_REG_RIP)
        return x64 ? "rip" : "eip";
    static const struct {
        unsigned r64;
        const char* n64;
        const char* n32;
    } table[] = {
        {X86_REG_RAX, "rax", "eax"}, {X86_REG_RBX, "rbx", "ebx"}, {X86_REG_RCX, "rcx", "ecx"},
        {X86_REG_RDX, "rdx", "edx"}, {X86_REG_RSI, "rsi", "esi"}, {X86_REG_RDI, "rdi", "edi"},
        {X86_REG_RBP, "rbp", "ebp"}, {X86_REG_RSP, "rsp", "esp"}, {X86_REG_R8, "r8", nullptr},
        {X86_REG_R9, "r9", nullptr}, {X86_REG_R10, "r10", nullptr}, {X86_REG_R11, "r11", nullptr},
        {X86_REG_R12, "r12", nullptr}, {X86_REG_R13, "r13", nullptr}, {X86_REG_R14, "r14", nullptr},
        {X86_REG_R15, "r15", nullptr},
    };
    for (const auto& t : table)
        if (regs::same_reg(r, t.r64))
            return x64 ? t.n64 : t.n32;
    return nullptr;
}

bool is_32bit_reg(unsigned r)
{
    switch (r) {
    case X86_REG_EAX: case X86_REG_EBX: case X86_REG_ECX: case X86_REG_EDX: case X86_REG_ESI: case X86_REG_EDI:
    case X86_REG_EBP: case X86_REG_ESP: case X86_REG_EIP: case X86_REG_R8D: case X86_REG_R9D: case X86_REG_R10D:
    case X86_REG_R11D: case X86_REG_R12D: case X86_REG_R13D: case X86_REG_R14D: case X86_REG_R15D:
        return true;
    default:
        return false;
    }
}

} // namespace

bool disassembler::writes(const uint8_t* buf, size_t n, uint64_t addr,
    const std::function<bool(const char* reg, uint64_t& value)>& reg, std::vector<mem_write>& out)
{
    out.clear();
    if (!handle_ || !buf || n == 0 || arch_ != bin_arch::x86)
        return false;
    const uint8_t* code = buf;
    size_t size = std::min<size_t>(n, 15);
    uint64_t a = addr;
    cs_insn* ci = (cs_insn*)scratch_;
    if (!cs_disasm_iter((csh)handle_, &code, &size, &a, ci))
        return false;
    const cs_detail* d = ci->detail;
    const cs_x86& x = d->x86;
    bool x64 = arch_ == bin_arch::x64;
    uint64_t ptr = x64 ? 8 : 4;
    auto value = [&](unsigned r, uint64_t& v) {
        const char* name = full_reg_name(r, x64);
        if (!name || !reg(name, v))
            return false;
        if (!x64 || is_32bit_reg(r))
            v &= 0xffffffffull;
        return true;
    };
    unsigned id = ci->id;

    // the kernel, or a far transfer, can write anywhere
    if (in_group(d, CS_GRP_INT) || id == X86_INS_SYSCALL || id == X86_INS_SYSENTER || id == X86_INS_INT ||
        id == X86_INS_INTO || id == X86_INS_LCALL || id == X86_INS_ENTER || id == X86_INS_MASKMOVDQU ||
        id == X86_INS_MASKMOVQ || id == X86_INS_VMASKMOVDQU)
        return false;

    // the stack: push and call write just below the stack pointer
    uint64_t sp = 0;
    uint32_t pushed = 0;
    if (id == X86_INS_CALL)
        pushed = (uint32_t)ptr;
    else if (id == X86_INS_PUSH)
        pushed = x.op_count && x.operands[0].size ? x.operands[0].size : (uint32_t)ptr;
    else if (id == X86_INS_PUSHFQ)
        pushed = 8;
    else if (id == X86_INS_PUSHFD)
        pushed = 4;
    else if (id == X86_INS_PUSHF)
        pushed = 2;
    else if (id == X86_INS_PUSHAL)
        pushed = 32;
    else if (id == X86_INS_PUSHAW)
        pushed = 16;
    if (pushed) {
        if (!value(x64 ? X86_REG_RSP : X86_REG_ESP, sp))
            return false;
        out.push_back({sp - pushed, pushed});
        if (id != X86_INS_PUSH) // a push can still read memory, but it writes only the stack
            return true;
    }

    // string writes: stos / movs, maybe repeated rcx times, up or down by the direction flag
    bool str = id == X86_INS_STOSB || id == X86_INS_STOSW || id == X86_INS_STOSD || id == X86_INS_STOSQ ||
               id == X86_INS_MOVSB || id == X86_INS_MOVSW || id == X86_INS_MOVSQ ||
               (id == X86_INS_MOVSD && x.op_count == 2 && x.operands[0].type == X86_OP_MEM && x.operands[1].type == X86_OP_MEM);
    if (str) {
        uint32_t elem = x.op_count ? x.operands[0].size : 0;
        if (!elem)
            return false;
        uint64_t di = 0, count = 1, flags = 0;
        if (!value(x64 ? X86_REG_RDI : X86_REG_EDI, di) || !reg("eflags", flags))
            return false;
        if (x.prefix[0] == X86_PREFIX_REP || x.prefix[0] == X86_PREFIX_REPNE) {
            if (!value(x64 ? X86_REG_RCX : X86_REG_ECX, count))
                return false;
            if (count == 0)
                return true; // nothing happens
        }
        if (count > (1u << 20) / elem)
            return false; // too much to keep
        uint64_t len = count * elem;
        bool down = (flags >> 10) & 1;
        out.push_back({down ? di + elem - len : di, (uint32_t)len});
        return true;
    }

    // everything else: memory operands it writes
    for (uint8_t i = 0; i < x.op_count && i < 8; i++) {
        const cs_x86_op& op = x.operands[i];
        if (op.type != X86_OP_MEM || !(op.access & CS_AC_WRITE))
            continue;
        if (op.mem.segment == X86_REG_FS || op.mem.segment == X86_REG_GS || op.size == 0)
            return false;
        uint64_t ea = (uint64_t)op.mem.disp;
        if (op.mem.base == X86_REG_RIP || op.mem.base == X86_REG_EIP) {
            ea += addr + ci->size;
        } else if (op.mem.base != X86_REG_INVALID) {
            uint64_t b = 0;
            if (!value(op.mem.base, b))
                return false;
            ea += b;
        }
        if (op.mem.index != X86_REG_INVALID) {
            uint64_t ix = 0;
            if (!value(op.mem.index, ix))
                return false;
            ea += ix * (uint64_t)op.mem.scale;
        }
        if (!x64)
            ea &= 0xffffffffull;
        out.push_back({ea, op.size});
    }
    return true;
}
