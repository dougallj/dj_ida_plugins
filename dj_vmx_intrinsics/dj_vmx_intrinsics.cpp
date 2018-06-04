// Hex-Rays VMX intrinsics plugin
// Copyright (c) Dougall Johnson, 2018

// NOTE: this generates "*a1 = __vmread(0x681Cui64)" instead of the
// correct "__vmx_vmread(0x681Eui64, a1)", both because I prefer the
// output, and because I had miscompilation problems when I generated
// "get address of register" operand arguments.

#include <hexrays.hpp>
#include <intel.hpp>

// Hex-Rays API pointer
hexdsp_t* hexdsp = NULL;

// Found by calling mop_t::dstr on sequential registers - it might be more
// portable to find it that way each time the plugin loads?
const mreg_t mr_tt = mreg_t(0xC0);

//--------------------------------------------------------------------------
class helpercall_builder_t {
public:
    helpercall_builder_t(codegen_t& _cdg, const char* name, tinfo_t return_type = tinfo_t(BT_VOID))
        : cdg(_cdg)
    {
        emitted = false;

        funcinfo = new mfuncinfo_t();
        funcinfo->callee = BADADDR;
        funcinfo->solid_args = 0;
        funcinfo->call_spd = 0;
        funcinfo->stkargs_top = 0;
        funcinfo->cc = CM_CC_FASTCALL,
        funcinfo->return_type = return_type;

        // FCI_PROP is used to avoid return-value verification,
        // since we may have already "propagated" it into a "mov"
        // instruction, I think.
        funcinfo->flags = FCI_FINAL | FCI_PROP;

        funcinfo->role = ROLE_UNK;

        // Prevent optimizing this away, even if the return value is unused.
        // unfortunately I'm not sure how to correctly spoil the regions
        // described in the documentation, so I just guess that this is enough.
        ivl_t glblow(0, 0x100000);
        funcinfo->spoiled.mem.add(glblow);

        callins = new_minsn(m_call);
        callins->l.make_helper(name);
        callins->d.t = mop_f;
        callins->d.size = 0;
        callins->d.f = funcinfo;

        if (return_type.is_void()) {
            ins = callins;
        } else {
            callins->d.size = (int)return_type.get_size();

            ins = new_minsn(m_mov);

            ins->l.t = mop_d;
            ins->l.d = callins;
            ins->l.size = callins->d.size;

            ins->d.t = mop_r;
            ins->d.r = 0;
            ins->d.size = callins->d.size;
        }
    }

    void add_register_argument(tinfo_t type, mreg_t reg)
    {
        mfuncarg_t* fa = &funcinfo->args.push_back();
        fa->t = mop_r;
        fa->r = reg;
        fa->type = type;
        fa->size = type.get_size();

        funcinfo->solid_args++;
    }

    void set_return_register(mreg_t reg)
    {
        if (ins->opcode != m_mov) {
            warning("helpercall_builder_t: cannot set_return_register for void return type");
            return;
        }
        ins->d.r = reg;
    }

    void emit()
    {
        if (emitted) {
            warning("helpercall_builder_t: cannot emit twice");
            return;
        }
        cdg.mb->insert_into_block(ins, cdg.mb->tail);
        emitted = true;
    }

    void emit_und_reg(mreg_t reg, int size)
    {
        minsn_t* ud_cf = new_minsn(m_und);
        ud_cf->d.t = mop_r;
        ud_cf->d.r = reg;
        ud_cf->d.size = size;

        cdg.mb->insert_into_block(ud_cf, cdg.mb->tail);
    }

    void emit_reg_equals_number(mreg_t result_reg, mreg_t reg, uint64 number, int size)
    {
        minsn_t* insn = new_minsn(m_setz);

        insn->l.t = mop_r;
        insn->l.r = reg;
        insn->l.size = size;

        insn->r.make_number(number, size);

        insn->d.t = mop_r;
        insn->d.r = result_reg;
        insn->d.size = 1;
        cdg.mb->insert_into_block(insn, cdg.mb->tail);
    }

    ~helpercall_builder_t()
    {
        // TODO: I guess if we didn't emit, we should delete these?
        cdg.mb->mark_lists_dirty();
    }

private:
    minsn_t* new_minsn(mcode_t opcode)
    {
        minsn_t* i = new minsn_t(cdg.insn.ea);
        i->opcode = opcode;

        // not sure if this is necessary, but to be safe:
        i->l.zero();
        i->r.zero();
        i->d.zero();
        return i;
    }

    bool emitted;
    codegen_t& cdg;
    mfuncinfo_t* funcinfo;
    minsn_t* callins;
    minsn_t* ins;
};

//--------------------------------------------------------------------------
static mreg_t hacky_store_operand(codegen_t& cdg, int operand)
{
    // "hacky" as this assumes load_operand either returns a register
    // operand, which is a valid destination register, or a temporary
    // register, which is the result of a load operand, and isn't used
    // in computing the address for that load operand.

    minsn_t* old_tail = cdg.mb->tail;

    mreg_t outreg = cdg.load_operand(operand);

    if (cdg.mb->tail == old_tail || !cdg.mb->tail || cdg.mb->tail->opcode != m_ldx) {
        // register destination
        return outreg;
    }

    // memory destination
    minsn_t* memop = cdg.mb->tail;

    memop->opcode = m_stx;

    mop_t sel = memop->l; // left
    mop_t off = memop->r; // right
    mop_t value = memop->d; // destination

    memop->l = value; // left
    memop->r = sel; // right
    memop->d = off; // destination

    return value.r;
}

//--------------------------------------------------------------------------
static mreg_t hacky_get_operand_address(codegen_t& cdg, int operand)
{
    minsn_t* old_tail = cdg.mb->tail;

    mreg_t outreg = cdg.load_operand(operand);

    if (cdg.mb->tail == old_tail || !cdg.mb->tail || cdg.mb->tail->opcode != m_ldx) {
        warning("hacky_get_operand_address failed! compilation output will be incorrect!");
        return outreg;
    }

    minsn_t* tail = cdg.mb->tail;

    // convert the m_ldx to a m_mov
    // TODO: is it safe to ignore the segment?
    tail->opcode = m_mov;
    tail->l = tail->r;
    tail->r.zero();
    tail->d.size = tail->l.size;

    return outreg;
}

//--------------------------------------------------------------------------
// Microsoft's VMX intrinsics return a byte:
//
// 0 = succeeded
// 1 = failed with status in VMCS
// 2 = failed with no status available
//
// So we generate:
//
// mov    call !__vmx_vmwrite<fast:"unsigned __int64" r9.8,"unsigned __int64" rax.8>.1, tt.1 ; 180001018 u=rax.8,r9.8 d=tt.1,(GLBLOW)
// setz   tt.1, #1.1, zf.1        ; 180001018 u=tt.1       d=zf.1
// setz   tt.1, #2.1, cf.1        ; 180001018 u=tt.1       d=cf.1
//
// However, their compiler generates the idiom:
//
// setz    cl
// setb    al
// adc     cl, al
//
// Leading to the following pattern in the output:
//
// v1 = __vmx_vmwrite(...);
// return (v1 == 2) + (v1 == 2) + (v1 == 1);
//
// This is technically correct, but we could do better. Possibly by matching
// the idiom, possibly by matching the AST (would need the 0 <= v1 < 3 data),
// possibly by generating it in a way that the existing optimizer could turn
// into (v1 & 3).
void do_ms_vmx_intrinsic_return(helpercall_builder_t& builder)
{
    builder.set_return_register(mr_tt);
    builder.emit_reg_equals_number(mr_zf, mr_tt, 1, 1);
    builder.emit_reg_equals_number(mr_cf, mr_tt, 2, 1);
}

//--------------------------------------------------------------------------
class vmread_filter_t : public microcode_filter_t {
public:
    virtual bool match(codegen_t& cdg)
    {
        return cdg.insn.itype == NN_vmread;
    }

    virtual merror_t apply(codegen_t& cdg)
    {
        helpercall_builder_t builder(cdg, "__vmread", tinfo_t(BT_INT64 | BTMT_USIGNED));
        builder.add_register_argument(tinfo_t(BT_INT64 | BTMT_USIGNED), cdg.load_operand(1));
        builder.emit();
        builder.set_return_register(hacky_store_operand(cdg, 0));
        builder.emit_und_reg(mr_cf, 1);
        builder.emit_und_reg(mr_zf, 1);
        return MERR_OK;
    }

    virtual ~vmread_filter_t() {}
};
static vmread_filter_t g_vmread_filter;

//--------------------------------------------------------------------------
class vmwrite_filter_t : public microcode_filter_t {
public:
    virtual bool match(codegen_t& cdg)
    {
        return cdg.insn.itype == NN_vmwrite;
    }

    virtual merror_t apply(codegen_t& cdg)
    {
        helpercall_builder_t builder(cdg, "__vmx_vmwrite", tinfo_t(BT_INT8 | BTMT_UNSIGNED));
        builder.add_register_argument(tinfo_t(BT_INT64 | BTMT_UNSIGNED), cdg.load_operand(0));
        builder.add_register_argument(tinfo_t(BT_INT64 | BTMT_UNSIGNED), cdg.load_operand(1));
        builder.emit();
        do_ms_vmx_intrinsic_return(builder);
        return MERR_OK;
    }

    virtual ~vmwrite_filter_t() {}
};
static vmwrite_filter_t g_vmwrite_filter;

//--------------------------------------------------------------------------
class vmcs_instr_filter_t : public microcode_filter_t {
public:
    virtual bool match(codegen_t& cdg)
    {
        return cdg.insn.itype == NN_vmptrld
            || cdg.insn.itype == NN_vmptrst
            || cdg.insn.itype == NN_vmxon
            || cdg.insn.itype == NN_vmclear;
    }

    virtual merror_t apply(codegen_t& cdg)
    {
        // TODO: __vmx_vmptrst doesn't return a value (but this shouldn't be a
        // problem in well-formed code)

        const char* name = NULL;
        switch (cdg.insn.itype) {
        case NN_vmptrld:
            name = "__vmx_vmptrld";
            break;
        case NN_vmptrst:
            name = "__vmx_vmptrst";
            break;
        case NN_vmxon:
            name = "__vmx_on";
            break;
        case NN_vmclear:
            name = "__vmx_vmclear";
            break;
        }

        helpercall_builder_t builder(cdg, name, tinfo_t(BT_INT8 | BTMT_UNSIGNED));
        // TODO: should be "unsigned __int64*"
        builder.add_register_argument(tinfo_t::get_stock(STI_PVOID), hacky_get_operand_address(cdg, 0));
        builder.emit();
        do_ms_vmx_intrinsic_return(builder);

        return MERR_OK;
    }

    virtual ~vmcs_instr_filter_t() {}
};
static vmcs_instr_filter_t g_vmcs_instr_filter;

//--------------------------------------------------------------------------
class vm_void_instr_filter_t : public microcode_filter_t {
public:
    virtual bool match(codegen_t& cdg)
    {
        // hex-rays already supports vmxoff/__vmx_off, as it doesn't have a return value
        return cdg.insn.itype == NN_vmlaunch
            || cdg.insn.itype == NN_vmresume;
    }

    virtual merror_t apply(codegen_t& cdg)
    {
        const char* name = NULL;
        switch (cdg.insn.itype) {
        case NN_vmlaunch:
            name = "__vmx_vmlaunch";
            break;
        case NN_vmresume:
            name = "__vmx_vmresume";
            break;
        }

        helpercall_builder_t builder(cdg, name, tinfo_t(BT_INT8 | BTMT_UNSIGNED));
        builder.emit();
        do_ms_vmx_intrinsic_return(builder);

        return MERR_OK;
    }

    virtual ~vm_void_instr_filter_t() {}
};
static vm_void_instr_filter_t g_vm_void_instr_filter;

//--------------------------------------------------------------------------
int idaapi init(void)
{
    if (ph.id != PLFM_386 || !inf.is_64bit())
        return false; // for x64 only

    if (!init_hexrays_plugin())
        return PLUGIN_SKIP; // no decompiler

    const char* hxver = get_hexrays_version();
    msg("Hex-rays version %s has been detected, %s ready to use\n", hxver, PLUGIN.wanted_name);

    install_microcode_filter(&g_vmread_filter, true);
    install_microcode_filter(&g_vmwrite_filter, true);
    install_microcode_filter(&g_vmcs_instr_filter, true);
    install_microcode_filter(&g_vm_void_instr_filter, true);
    return PLUGIN_KEEP;
}

//--------------------------------------------------------------------------
void idaapi term(void)
{
    if (hexdsp != NULL) {
        install_microcode_filter(&g_vm_void_instr_filter, false);
        install_microcode_filter(&g_vmcs_instr_filter, false);
        install_microcode_filter(&g_vmwrite_filter, false);
        install_microcode_filter(&g_vmread_filter, false);
        term_hexrays_plugin();
    }
}

//--------------------------------------------------------------------------
bool idaapi run(size_t)
{
    warning("The '%s' plugin is fully automatic", PLUGIN.wanted_name);
    return false;
}

//--------------------------------------------------------------------------
static const char comment[] = "VMX intrinsics plugin for Hex-Rays decompiler";

//--------------------------------------------------------------------------
//
//      PLUGIN DESCRIPTION BLOCK
//
//--------------------------------------------------------------------------
plugin_t PLUGIN = {
    IDP_INTERFACE_VERSION,
    PLUGIN_HIDE, // plugin flags
    init, // initialize
    term, // terminate. this pointer may be NULL.
    run, // invoke plugin
    comment,
    "VMX intrinsics", // the preferred short name of the plugin
    "" // the preferred hotkey to run the plugin
};
