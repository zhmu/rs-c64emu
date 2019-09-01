use std::io;
use std::io::prelude::*;
use std::fs::File;

type Cycles = i8;
type Address = u16;
type Flags = u8;

const MEMORY_SIZE: usize = 65536;

#[derive(Debug)]
pub enum MemoryLoadError {
    IoError(io::Error),
    InvalidSize
}

#[derive(Debug)]
pub enum MOS6502Error {
    IllegalOpcode(u8),
    WriteToROM(Address, u8),
    InvalidRead(Address)
}

pub struct Memory {
    data: [ u8; MEMORY_SIZE ]
}

fn make_u16(first: u8, second: u8) -> u16 {
    ((first as u16) | ((second as u16) << 8))
}

impl Memory {
    pub fn new() -> Memory {
        let data: [ u8; MEMORY_SIZE ] = [ 0; MEMORY_SIZE ];
        Memory{ data }
    }

    pub fn load_rom(&mut self, base: Address, path: &str) -> Result<(), MemoryLoadError> {
        let mut f = File::open(path).map_err(MemoryLoadError::IoError)?;

        let mut buffer = Vec::new();
        f.read_to_end(&mut buffer).map_err(MemoryLoadError::IoError)?;
        if base as usize + buffer.len() > MEMORY_SIZE {
            return Err(MemoryLoadError::InvalidSize)
        }

        // XXX I'm sure we can do this in a more efficient way
        for n in 0..buffer.len() {
            self.data[base as usize + n] = buffer[n];
        }

        Ok(())
    }

    fn get_u8(&mut self, address: Address) -> Result<u8, MOS6502Error> {
        match address {
            0xd012 => Ok(0), // XXX read raster/writer raster IRQ compare value
            _ => Ok(self.data[address as usize])
        }
    }

    pub fn read_u8(&self, address: Address) -> u8 {
        self.data[address as usize]
    }

    fn get_u16(&mut self, address: Address) -> Result<u16, MOS6502Error> {
        let a = self.get_u8(address + 0)?;
        let b = self.get_u8(address + 1)?;
        Ok(make_u16(a, b))
    }

    pub fn set_u8(&mut self, address: Address, data: u8) -> Result<(), MOS6502Error> {
        // TODO check ROM etc
        //Err(MOS6502Error::WriteToROM(address, data))
        self.data[address as usize] = data;
        Ok(())
    }
}

//const VECTOR_NMI: Address = 0xfffa;
const VECTOR_RESET: Address = 0xfffc;
const VECTOR_IRQ_BRK: Address = 0xfffe;

const STACK_BASE: Address = 0x100;

const FLAG_N: Flags = 0x80;
const FLAG_V: Flags = 0x40;
const FLAG_1: Flags = 0x20; // always 1
const FLAG_B: Flags = 0x10;
const FLAG_D: Flags = 0x08;
const FLAG_I: Flags = 0x04;
const FLAG_Z: Flags = 0x02;
const FLAG_C: Flags = 0x01;

struct Registers {
    a: u8,
    x: u8,
    y: u8,
    fl: Flags,
    pc: Address,
    sp: Address,
}

impl Registers {
    pub fn new() -> Registers {
        Registers{ a: 0, x: 0, y: 0, fl: FLAG_1, pc: 0, sp: STACK_BASE + 0xff}
    }

    fn set_flag(&mut self, flag: u8) {
        self.fl = self.fl | flag;
    }

    fn clear_flag(&mut self, flag: u8) {
        self.fl = self.fl & !flag;
    }

    fn set_or_clear_flag(&mut self, flag: u8, set: bool) {
        if set {
            self.set_flag(flag);
        } else {
            self.clear_flag(flag);
        }
    }

    fn update_flags_nz(&mut self, value: u8) {
        self.set_or_clear_flag(FLAG_N, value >= 0x80);
        self.set_or_clear_flag(FLAG_Z, value == 0);
    }
}

pub struct MOS6502 {
    regs: Registers
}

impl MOS6502 {
    pub fn new() -> MOS6502 {
        MOS6502{ regs: Registers::new() }
    }

    pub fn execute(&mut self, mem: &mut Memory) -> Result<Cycles, MOS6502Error> {
        match self.fetch_pc_u8(mem)? {
            0x00 => /* BRK */        { self.push_u16(mem, self.regs.pc + 2)?; self.push_u8(mem, self.regs.fl)?; self.regs.clear_flag(FLAG_I); self.regs.pc = mem.get_u16(VECTOR_IRQ_BRK)?; Ok(7) },
            0x01 => /* ORA (in,X) */ { let m = self.get_in_x(mem)?; self.do_ora(m); Ok(6) }
            0x05 => /* ORA zp     */ { let m = self.get_zp(mem)?; self.do_ora(m); Ok(3) }
            0x06 => /* ASL zp     */ { self.apply_zp(mem, do_asl)?; Ok(5) },
            0x08 => /* PHP        */ { self.push_u8(mem, self.regs.fl)?; Ok(3) },
            0x09 => /* ORA #imm   */ { let m = self.get_imm(mem)?; self.do_ora(m); Ok(2) },
            0x0a => /* ASL a      */ { self.apply_a(mem, do_asl)?; Ok(2) },
            0x0d => /* ORA abs    */ { let m = self.get_abs(mem)?; self.do_ora(m); Ok(4) }
            0x0e => /* ASL abs    */ { self.apply_abs(mem, do_asl)?; Ok(6) },
            0x10 => /* BPL rel    */ { let cyc = self.do_branch(mem, (self.regs.fl & FLAG_N) == 0)?; Ok(2 + cyc) },
            0x11 => /* ORA (in),Y */ { let (m, cyc) = self.get_in_y(mem)?; self.do_ora(m); Ok(5 + cyc) },
            0x15 => /* ORA zp,X   */ { let m = self.get_zp_x(mem, )?; self.do_ora(m); Ok(4) },
            0x16 => /* ASL zp,X   */ { self.apply_zp_x(mem, do_asl)?; Ok(5) },
            0x18 => /* CLC        */ { self.regs.clear_flag(FLAG_C); Ok(2) },
            0x19 => /* ORA abs,Y  */ { let (m, cyc) = self.get_abs_y(mem)?; self.do_ora(m); Ok(4 + cyc) },
            0x1d => /* ORA abs,X  */ { let (m, cyc) = self.get_abs_x(mem)?; self.do_ora(m); Ok(4 + cyc) },
            0x1e => /* ASL abs,X  */ { self.apply_abs_x(mem, do_asl)?; Ok(7) },
            0x20 => /* JSR abs    */ { let m = self.fetch_pc_u16(mem)?; self.push_u16(mem, self.regs.pc - 1)?; self.regs.pc = m; Ok(6) },
            0x21 => /* AND (in,X) */ { let m = self.get_in_x(mem)?; self.do_and(m); Ok(6) },
            0x24 => /* BIT zp     */ { let m = self.get_zp(mem)?; self.do_bit(m); Ok(3) },
            0x25 => /* AND zp     */ { let m = self.get_zp(mem)?; self.do_and(m); Ok(3) },
            0x26 => /* ROL zp     */ { self.apply_zp(mem, do_rol)?; Ok(5) },
            0x28 => /* PLP        */ { let fl = self.pop_u8(mem)?; self.regs.fl = fl | FLAG_1; Ok(4) },
            0x29 => /* AND #imm   */ { let m = self.get_imm(mem)?; self.do_and(m); Ok(2) },
            0x2a => /* ROL a      */ { self.apply_a(mem, do_rol)?; Ok(2) },
            0x2c => /* BIT abs    */ { let m = self.get_abs(mem)?; self.do_bit(m); Ok(4) },
            0x2d => /* AND abs    */ { let m = self.get_abs(mem)?; self.do_and(m); Ok(4) },
            0x2e => /* ROL abs    */ { self.apply_abs(mem, do_rol)?; Ok(6) },
            0x30 => /* BMI rel    */ { let cyc = self.do_branch(mem, (self.regs.fl & FLAG_N) != 0)?; Ok(2 + cyc) },
            0x31 => /* AND (in),Y */ { let (m, cyc) = self.get_in_y(mem)?; self.do_and(m); Ok(5 + cyc) },
            0x35 => /* AND zp,X   */ { let m = self.get_zp_x(mem, )?; self.do_and(m); Ok(4) },
            0x36 => /* ROL zp,X   */ { self.apply_zp_x(mem, do_rol)?; Ok(6) },
            0x38 => /* SEC        */ { self.regs.set_flag(FLAG_C); Ok(2) },
            0x39 => /* AND abs,Y  */ { let (m, cyc) = self.get_abs_y(mem)?; self.do_and(m); Ok(4 + cyc) }
            0x3d => /* AND abs,X  */ { let (m, cyc) = self.get_abs_x(mem)?; self.do_and(m); Ok(4 + cyc) }
            0x3e => /* ROL abs,X  */ { self.apply_abs_x(mem, do_rol)?; Ok(7) },
            0x40 => /* RTI        */ { let fl = self.pop_u8(mem)?; let pc = self.pop_u16(mem)?; self.regs.fl = fl | FLAG_1; self.regs.pc = pc; Ok(6) },
            0x41 => /* EOR (in,X) */ { let m = self.get_in_x(mem)?; self.do_eor(m); Ok(6) }
            0x45 => /* EOR zp     */ { let m = self.get_zp(mem)?; self.do_eor(m); Ok(3) }
            0x46 => /* LSR zp     */ { self.apply_zp(mem, do_lsr)?; Ok(5) },
            0x48 => /* PHA        */ { self.push_u8(mem, self.regs.a)?; Ok(3) },
            0x49 => /* EOR #imm   */ { let m = self.get_imm(mem)?; self.do_eor(m); Ok(2) },
            0x4a => /* LSR a      */ { self.apply_a(mem, do_lsr)?; Ok(2) },
            0x4c => /* JMP abs    */ { self.regs.pc = self.fetch_pc_u16(mem)?; Ok(3) }
            0x4d => /* EOR abs    */ { let m = self.get_abs(mem)?; self.do_eor(m); Ok(4) },
            0x4e => /* LSR abs    */ { self.apply_abs(mem, do_lsr)?; Ok(6) },
            0x50 => /* BVC rel    */ { let cyc = self.do_branch(mem, (self.regs.fl & FLAG_V) == 0)?; Ok(2 + cyc) },
            0x51 => /* EOR (in),Y */ { let (m, cyc) = self.get_in_y(mem)?; self.do_eor(m); Ok(5 + cyc) },
            0x55 => /* EOR zp,X   */ { let m = self.get_zp_x(mem, )?; self.do_eor(m); Ok(4) },
            0x56 => /* LSR zp,X   */ { self.apply_zp_x(mem, do_lsr)?; Ok(6) },
            0x58 => /* CLI        */ { self.regs.clear_flag(FLAG_I); Ok(2) },
            0x59 => /* EOR abs,Y  */ { let (m, cyc) = self.get_abs_y(mem)?; self.do_eor(m); Ok(4 + cyc) }
            0x5d => /* EOR abs,X  */ { let (m, cyc) = self.get_abs_x(mem)?; self.do_eor(m); Ok(4 + cyc) }
            0x5e => /* LSR abs,X  */ { self.apply_abs_x(mem, do_lsr)?; Ok(7) },
            0x60 => /* RTS        */ { let ret = self.pop_u16(mem)?; self.regs.pc = ret + 1; Ok(6) },
            0x61 => /* ADC (in,X) */ { let m = self.get_in_x(mem)?; self.do_adc(m); Ok(6) },
            0x65 => /* ADC zp     */ { let m = self.get_zp(mem)?; self.do_adc(m); Ok(3) },
            0x66 => /* ROR zp     */ { self.apply_zp(mem, do_ror)?; Ok(5) },
            0x68 => /* PLA        */ { self.regs.a = self.pop_u8(mem)?; Ok(4) },
            0x69 => /* ADC #imm   */ { let m = self.get_imm(mem)?; self.do_adc(m); Ok(2) },
            0x6a => /* ROR a      */ { self.apply_a(mem, do_ror)?; Ok(2) },
            0x6c => /* JMP (abs)  */ { let m = self.fetch_pc_u16(mem)?; let v = mem.get_u16(m)?; self.regs.pc = v; Ok(5) },
            0x6d => /* ADC abs    */ { let m = self.get_abs(mem)?; self.do_adc(m); Ok(4) },
            0x6e => /* ROR abs    */ { self.apply_abs(mem, do_ror)?; Ok(6) },
            0x70 => /* BVS rel    */ { let cyc = self.do_branch(mem, (self.regs.fl & FLAG_V) != 0)?; Ok(2 + cyc) },
            0x71 => /* ADC (in),Y */ { let (m, cyc) = self.get_in_y(mem)?; self.do_adc(m); Ok(5 + cyc) },
            0x75 => /* ADC zp,X   */ { let m = self.get_zp_x(mem, )?; self.do_adc(m); Ok(4) },
            0x76 => /* ROR zp,X   */ { self.apply_zp_x(mem, do_ror)?; Ok(6) },
            0x78 => /* SEI        */ { self.regs.set_flag(FLAG_I); Ok(2) },
            0x79 => /* ADC abs,Y  */ { let (m, cyc) = self.get_abs_y(mem)?; self.do_adc(m); Ok(4 + cyc) },
            0x7d => /* ADC abs,X  */ { let (m, cyc) = self.get_abs_x(mem)?; self.do_adc(m); Ok(4 + cyc) },
            0x7e => /* ROR abs,X  */ { self.apply_abs_x(mem, do_ror)?; Ok(7) },
            0x81 => /* STA (in,X) */ { self.apply_in_x(mem, do_sta)?; Ok(6) },
            0x84 => /* STY zp     */ { self.apply_zp(mem, do_sty)?; Ok(3) },
            0x85 => /* STA zp     */ { self.apply_zp(mem, do_sta)?; Ok(3) },
            0x86 => /* STX zp     */ { self.apply_zp(mem, do_stx)?; Ok(3) },
            0x88 => /* DEY        */ { self.regs.y = self.regs.y.wrapping_sub(1); self.regs.update_flags_nz(self.regs.y); Ok(2) },
            0x8a => /* TXA        */ { self.regs.a = self.regs.x; self.regs.update_flags_nz(self.regs.a); Ok(2) },
            0x8c => /* STY abs    */ { self.apply_abs(mem, do_sty)?; Ok(4) },
            0x8d => /* STA abs    */ { self.apply_abs(mem, do_sta)?; Ok(4) },
            0x8e => /* STX abs    */ { self.apply_abs(mem, do_stx)?; Ok(4) },
            0x90 => /* BCC rel    */ { let cyc = self.do_branch(mem, (self.regs.fl & FLAG_C) == 0)?; Ok(2 + cyc) },
            0x91 => /* STA (in),Y */ { self.apply_in_y(mem, do_sta)?; Ok(6) },
            0x94 => /* STY zp,X   */ { self.apply_zp_x(mem, do_sty)?; Ok(4) },
            0x95 => /* STA zp,X   */ { self.apply_zp_x(mem, do_sta)?; Ok(4) },
            0x96 => /* STX zp,Y   */ { self.apply_zp_y(mem, do_stx)?; Ok(4) },
            0x98 => /* TYA        */ { self.regs.a = self.regs.y; self.regs.update_flags_nz(self.regs.a); Ok(2) },
            0x99 => /* STA abs,Y  */ { self.apply_abs_y(mem, do_sta)?; Ok(5) },
            0x9a => /* TXS        */ { self.regs.sp = STACK_BASE + self.regs.x as Address; Ok(2) },
            0x9d => /* STA abs,X  */ { self.apply_abs_x(mem, do_sta)?; Ok(5) },
            0xa0 => /* LDY #imm   */ { let m = self.get_imm(mem)?; self.do_ldy(m); Ok(2) },
            0xa1 => /* LDA (in,X) */ { let m = self.get_in_x(mem)?; self.do_lda(m); Ok(6) },
            0xa2 => /* LDX #imm   */ { let m = self.get_imm(mem)?; self.do_ldx(m); Ok(2) },
            0xa4 => /* LDY zp     */ { let m = self.get_zp(mem)?; self.do_ldy(m); Ok(3) },
            0xa5 => /* LDA zp     */ { let m = self.get_zp(mem)?; self.do_lda(m); Ok(3) },
            0xa6 => /* LDX zp     */ { let m = self.get_zp(mem)?; self.do_ldx(m); Ok(3) },
            0xa8 => /* TAY        */ { self.regs.y = self.regs.a; self.regs.update_flags_nz(self.regs.y); Ok(2) },
            0xa9 => /* LDA #imm   */ { let m = self.get_imm(mem)?; self.do_lda(m); Ok(2) },
            0xaa => /* TAX        */ { self.regs.x = self.regs.a; self.regs.update_flags_nz(self.regs.x); Ok(2) },
            0xac => /* LDY abs    */ { let m = self.get_abs(mem)?; self.do_ldy(m); Ok(4) },
            0xad => /* LDA abs    */ { let m = self.get_abs(mem)?; self.do_lda(m); Ok(4) },
            0xae => /* LDX abs    */ { let m = self.get_abs(mem)?; self.do_ldx(m); Ok(4) },
            0xb0 => /* BCS rel    */ { let cyc = self.do_branch(mem, (self.regs.fl & FLAG_C) != 0)?; Ok(2 + cyc) },
            0xb1 => /* LDA (in),Y */ { let (m, cyc) = self.get_in_y(mem)?; self.do_lda(m); Ok(5 + cyc) },
            0xb4 => /* LDY zp,X   */ { let m = self.get_zp_x(mem, )?; self.do_ldy(m); Ok(4) },
            0xb5 => /* LDA zp,X   */ { let m = self.get_zp_x(mem, )?; self.do_lda(m); Ok(4) },
            0xb6 => /* LDX zp,Y   */ { let m = self.get_zp_y(mem, )?; self.do_ldx(m); Ok(4) },
            0xb8 => /* CLV        */ { self.regs.clear_flag(FLAG_V); Ok(2) },
            0xb9 => /* LDA abs,Y  */ { let (m, cyc) = self.get_abs_y(mem)?; self.do_lda(m); Ok(4 + cyc) },
            0xba => /* TSX        */ { self.regs.x = (self.regs.sp & 0xff) as u8; Ok(2) }, // XXX set flags?
            0xbc => /* LDY abs,X  */ { let (m, cyc) = self.get_abs_x(mem)?; self.do_ldy(m); Ok(4 + cyc) },
            0xbd => /* LDA abs,X  */ { let (m, cyc) = self.get_abs_x(mem)?; self.do_lda(m); Ok(4 + cyc) },
            0xbe => /* LDX abs,Y  */ { let (m, cyc) = self.get_abs_y(mem)?; self.do_ldx(m); Ok(4 + cyc) },
            0xc0 => /* CPY #imm   */ { let m = self.get_imm(mem)?; self.do_cpy(m); Ok(2) },
            0xc1 => /* CMP (in,X) */ { let m = self.get_in_x(mem)?; self.do_cmp(m); Ok(6) },
            0xc4 => /* CPY zp     */ { let m = self.get_zp(mem)?; self.do_cpy(m); Ok(3) },
            0xc5 => /* CMP zp     */ { let m = self.get_zp(mem)?; self.do_cmp(m); Ok(3) },
            0xc6 => /* DEC zp     */ { self.apply_zp(mem, do_dec)?; Ok(5) },
            0xc8 => /* INY        */ { self.regs.y = self.regs.y.wrapping_add(1); self.regs.update_flags_nz(self.regs.y); Ok(2) },
            0xc9 => /* CMP #imm   */ { let m = self.get_imm(mem)?; self.do_cmp(m); Ok(2) },
            0xca => /* DEX        */ { self.regs.x = self.regs.x.wrapping_sub(1); self.regs.update_flags_nz(self.regs.x); Ok(2) },
            0xcc => /* CPY abs    */ { let m = self.get_abs(mem)?; self.do_cpy(m); Ok(4) },
            0xcd => /* CMP abs    */ { let m = self.get_abs(mem)?; self.do_cmp(m); Ok(4) },
            0xce => /* DEC abs    */ { self.apply_abs(mem, do_dec)?; Ok(6) },
            0xd0 => /* BNE rel    */ { let cyc = self.do_branch(mem, (self.regs.fl & FLAG_Z) == 0)?; Ok(2 + cyc) },
            0xd1 => /* CMP (in),Y */ { let (m, cyc) = self.get_in_y(mem)?; self.do_cmp(m); Ok(5 + cyc) },
            0xd5 => /* CMP zp,X   */ { let m = self.get_zp_x(mem, )?; self.do_cmp(m); Ok(4) },
            0xd6 => /* DEC zp,X   */ { self.apply_zp_x(mem, do_dec)?; Ok(6) },
            0xd8 => /* CLD        */ { self.regs.clear_flag(FLAG_D); Ok(2) },
            0xd9 => /* CMP abs,Y  */ { let (m, cyc) = self.get_abs_y(mem)?; self.do_cmp(m); Ok(4 + cyc) },
            0xdd => /* CMP abs,X  */ { let (m, cyc) = self.get_abs_x(mem)?; self.do_cmp(m); Ok(4 + cyc) },
            0xde => /* DEC abs,X  */ { self.apply_abs_x(mem, do_dec)?; Ok(7) },
            0xe0 => /* CPX #imm   */ { let m = self.get_imm(mem)?; self.do_cpx(m); Ok(2) },
            0xe1 => /* SBC (in,X) */ { let m = self.get_in_x(mem)?; self.do_sbc(m); Ok(6) },
            0xe4 => /* CPX zp     */ { let m = self.get_zp(mem)?; self.do_cpx(m); Ok(3) },
            0xe5 => /* SBC zp     */ { let m = self.get_zp(mem)?; self.do_sbc(m); Ok(3) },
            0xe6 => /* INC zp     */ { self.apply_zp(mem, do_inc)?; Ok(5) },
            0xe8 => /* INX        */ { self.regs.x = self.regs.x.wrapping_add(1); self.regs.update_flags_nz(self.regs.x); Ok(2) },
            0xe9 => /* SBC #imm   */ { let m = self.get_imm(mem)?; self.do_sbc(m); Ok(2) },
            0xea => /* NOP        */ { Ok(2) },
            0xec => /* CPX abs    */ { let m = self.get_abs(mem)?; self.do_cpx(m); Ok(4) },
            0xed => /* SBC abs    */ { let m = self.get_abs(mem)?; self.do_sbc(m); Ok(4) },
            0xee => /* INC abs    */ { self.apply_abs(mem, do_inc)?; Ok(6) },
            0xf0 => /* BEQ rel    */ { let cyc = self.do_branch(mem, (self.regs.fl & FLAG_Z) != 0)?; Ok(2 + cyc) },
            0xf1 => /* SBC (in),Y */ { let (m, cyc) = self.get_in_y(mem)?; self.do_sbc(m); Ok(5 + cyc) },
            0xf5 => /* SBC zp,X   */ { let m = self.get_zp_x(mem, )?; self.do_sbc(m); Ok(4) },
            0xf6 => /* INC zp,X   */ { self.apply_zp_x(mem, do_inc)?; Ok(6) },
            0xf8 => /* SED        */ { self.regs.set_flag(FLAG_D); Ok(2) },
            0xf9 => /* SBC abs,Y  */ { let (m, cyc) = self.get_abs_y(mem)?; self.do_sbc(m); Ok(4 + cyc) },
            0xfd => /* SBC abs,X  */ { let (m, cyc) = self.get_abs_x(mem)?; self.do_sbc(m); Ok(4 + cyc) },
            0xfe => /* INC abs,X  */ { self.apply_abs_x(mem, do_inc)?; Ok(7) },
            op => Err(MOS6502Error::IllegalOpcode(op))
        }
    }

    fn do_ora(&mut self, m: u8) {
        self.regs.a |= m;
        self.regs.update_flags_nz(self.regs.a);
    }

    fn do_and(&mut self, m: u8) {
        self.regs.a &= m;
        self.regs.update_flags_nz(self.regs.a);
    }

    fn do_eor(&mut self, m: u8) {
        self.regs.a ^= m;
        self.regs.update_flags_nz(self.regs.a);
    }

    fn do_bit(&mut self, m: u8) {
        self.regs.set_or_clear_flag(FLAG_N, (m & 0x80) != 0);
        self.regs.set_or_clear_flag(FLAG_V, (m & 0x40) != 0);
        self.regs.set_or_clear_flag(FLAG_Z, (m & self.regs.a) == 0);
    }

    fn do_adc(&mut self, m: u8) {
        let mut v = self.regs.a as u16 + m as u16;
        if (self.regs.fl & FLAG_C) != 0 {
            v += 1;
        }
        self.regs.a = (v & 0xff) as u8;
        self.regs.update_flags_nz(self.regs.a);
        self.regs.set_or_clear_flag(FLAG_C, v >= 0x100);
        let w = v as i16;
        self.regs.set_or_clear_flag(FLAG_V, w < -128 || w > 128);
    }

    fn do_sbc(&mut self, m: u8) {
        let mut v = (self.regs.a as i16) - m as i16;
        if (self.regs.fl & FLAG_C) != 0 {
            v -= 1;
        }
        self.regs.a = ((v as u16) & 0xff) as u8;
        self.regs.update_flags_nz(self.regs.a);
        self.regs.set_or_clear_flag(FLAG_C, v >= 0);
        self.regs.set_or_clear_flag(FLAG_V, v < -128 || v > 128);
    }

    fn do_lda(&mut self, m: u8) {
        self.regs.a = m;
        self.regs.update_flags_nz(self.regs.a);
    }

    fn do_ldx(&mut self, m: u8) {
        self.regs.x = m;
        self.regs.update_flags_nz(self.regs.x);
    }

    fn do_ldy(&mut self, m: u8) {
        self.regs.y = m;
        self.regs.update_flags_nz(self.regs.y);
    }

    fn do_compare(&mut self, src: u8, imm: u8) {
        let v = src.wrapping_sub(imm);
        self.regs.set_or_clear_flag(FLAG_C, src >= imm);
        self.regs.update_flags_nz(v);
    }

    fn do_cmp(&mut self, m: u8) {
        self.do_compare(self.regs.a, m)
    }

    fn do_cpx(&mut self, m: u8) {
        self.do_compare(self.regs.x, m)
    }

    fn do_cpy(&mut self, m: u8) {
        self.do_compare(self.regs.y, m)
    }

    
    fn do_branch(&mut self, mem: &mut Memory, take: bool) -> Result<Cycles, MOS6502Error> {
        let val = self.fetch_pc_u8(mem)? as i8;
        if take {
            // TODO: add 1 if the branch occurs on the same page
            self.regs.pc = self.regs.pc.wrapping_add(val as u16);
            return Ok(1);
        }
        Ok(0)
    }

    pub fn reset(&mut self, mem: &mut Memory) -> Result<(), MOS6502Error> {
        self.regs.a = 0;
        self.regs.x = 0;
        self.regs.y = 0;
        self.regs.fl = FLAG_1;
        self.regs.pc = mem.get_u16(VECTOR_RESET)?;
        self.regs.sp = 0x100;
        Ok(())
    }

    fn fetch_pc_u8(&mut self, mem: &mut Memory) -> Result<u8, MOS6502Error> {
        let d = mem.get_u8(self.regs.pc)?;
        self.regs.pc += 1;
        Ok(d)
    }

    fn fetch_pc_u16(&mut self, mem: &mut Memory) -> Result<u16, MOS6502Error> {
        let d = mem.get_u16(self.regs.pc)?;
        self.regs.pc += 2;
        Ok(d)
    }

    // zp
    fn get_zp(&mut self, mem: &mut Memory) -> Result<u8, MOS6502Error> {
        let v = self.fetch_pc_u8(mem)?;
        mem.get_u8(v as Address)
    }

    // zp,X
    fn get_zp_x(&mut self, mem: &mut Memory) -> Result<u8, MOS6502Error> {
        let v = (self.fetch_pc_u8(mem)? as u16 + self.regs.x as u16) & 0xff;
        mem.get_u8(v)
    }

    // zp,Y
    fn get_zp_y(&mut self, mem: &mut Memory) -> Result<u8, MOS6502Error> {
        let v = (self.fetch_pc_u8(mem)? + self.regs.y) & 0xff;
        mem.get_u8(v as Address)
    }

    // (in,X)
    fn get_in_x(&mut self, mem: &mut Memory) -> Result<u8, MOS6502Error> {
        let v = (self.fetch_pc_u8(mem)? + self.regs.x) & 0xff;
        let a = mem.get_u16(v as Address)?;
        mem.get_u8(a)
    }

    // (in),Y
    fn get_in_y(&mut self, mem: &mut Memory) -> Result<(u8, Cycles), MOS6502Error> {
        let a = self.fetch_pc_u8(mem)? as Address;
        let b = mem.get_u16(a)?;
        let v = mem.get_u8(b + self.regs.y as Address)?;
        Ok((v, 0 /* TODO cyles */))
    }

    // abs,Y
    fn get_abs_y(&mut self, mem: &mut Memory) -> Result<(u8, Cycles), MOS6502Error> {
        let a = self.fetch_pc_u16(mem)?;
        let v = mem.get_u8(a + self.regs.y as Address)?;
        Ok((v, 0 /* TODO cycles */))
    }

    // abs, X
    fn get_abs_x(&mut self, mem: &mut Memory) -> Result<(u8, Cycles), MOS6502Error> {
        let a = self.fetch_pc_u16(mem)?;
        let v = mem.get_u8(a + self.regs.x as Address)?;
        Ok((v, 0 /* TODO cycles */))
    }

    fn get_abs(&mut self, mem: &mut Memory) -> Result<u8, MOS6502Error> {
        let d = self.fetch_pc_u16(mem)?;
        mem.get_u8(d)
    }

    fn get_imm(&mut self, mem: &mut Memory) -> Result<u8, MOS6502Error> {
        self.fetch_pc_u8(mem)
    }

    fn push_u8(&mut self, mem: &mut Memory, v: u8) -> Result<(), MOS6502Error> {
        mem.set_u8(self.regs.sp, v)?;
        self.regs.sp -= 1;
        Ok(())
    }

    fn push_u16(&mut self, mem: &mut Memory, v: u16) -> Result<(), MOS6502Error> {
        self.push_u8(mem, (v >> 8) as u8)?;
        self.push_u8(mem, (v & 0xff) as u8)?;
        Ok(())
    }

    fn pop_u8(&mut self, mem: &mut Memory) -> Result<u8, MOS6502Error> {
        let v = mem.get_u8(self.regs.sp + 1)?;
        self.regs.sp += 1;
        Ok(v)
    }

    fn pop_u16(&mut self, mem: &mut Memory) -> Result<u16, MOS6502Error> {
        let a = mem.get_u8(self.regs.sp + 1)?;
        let b = mem.get_u8(self.regs.sp + 2)?;
        self.regs.sp += 2;
        Ok(make_u16(a, b))
    }

    // mem[addr] = f(mem[addr])
    fn apply_addr(&mut self, mem: &mut Memory, addr: Address, f: impl Fn(&mut Registers, u8) -> u8) -> Result<(), MOS6502Error> {
        let v = mem.get_u8(addr)?;
        let v = f(&mut self.regs, v);
        mem.set_u8(addr, v)
    }

    // regs.a = f(regs.a)
    fn apply_a(&mut self, _mem: &mut Memory, f: impl Fn(&mut Registers, u8) -> u8) -> Result<(), MOS6502Error> {
        let a = self.regs.a;
        let v = f(&mut self.regs, a);
        self.regs.a = v;
        Ok(())
    }

    // zp = f(zp)
    fn apply_zp(&mut self, mem: &mut Memory, f: impl Fn(&mut Registers, u8) -> u8) -> Result<(), MOS6502Error> {
        let addr = self.fetch_pc_u8(mem)? as Address;
        self.apply_addr(mem, addr, f)
    }

    // zp,x = f(zp,x)
    fn apply_zp_x(&mut self, mem: &mut Memory, f: impl Fn(&mut Registers, u8) -> u8) -> Result<(), MOS6502Error> {
        let a = self.fetch_pc_u8(mem)?;
        let addr = ((a + self.regs.x) & 0xff) as Address;
        self.apply_addr(mem, addr, f)
    }

    // zp,y = f(zp,y)
    fn apply_zp_y(&mut self, mem: &mut Memory, f: impl Fn(&mut Registers, u8) -> u8) -> Result<(), MOS6502Error> {
        let a = self.fetch_pc_u8(mem)?;
        let addr = ((a + self.regs.y) & 0xff) as Address;
        self.apply_addr(mem, addr, f)
    }

    // *abs = f(*abs)
    fn apply_abs(&mut self, mem: &mut Memory, f: impl Fn(&mut Registers, u8) -> u8) -> Result<(), MOS6502Error> {
        let addr = self.fetch_pc_u16(mem)?;
        self.apply_addr(mem, addr, f)
    }

    fn apply_abs_x(&mut self, mem: &mut Memory, f: impl Fn(&mut Registers, u8) -> u8) -> Result<(), MOS6502Error> {
        let addr = self.fetch_pc_u16(mem)?;
        let addr = addr + self.regs.x as Address; // XXX what about extra cycles?
        self.apply_addr(mem, addr, f)
    }

    fn apply_abs_y(&mut self, mem: &mut Memory, f: impl Fn(&mut Registers, u8) -> u8) -> Result<(), MOS6502Error> {
        let addr = self.fetch_pc_u16(mem)?;
        let addr = addr + self.regs.y as Address; // XXX what about extra cycles?
        self.apply_addr(mem, addr, f)
    }

    fn apply_in_x(&mut self, mem: &mut Memory, f: impl Fn(&mut Registers, u8) -> u8) -> Result<(), MOS6502Error> {
        let a = self.fetch_pc_u8(mem)? as Address;
        let addr = (a + self.regs.x as Address) & 0xff;
        self.apply_addr(mem, addr, f)
    }

    fn apply_in_y(&mut self, mem: &mut Memory, f: impl Fn(&mut Registers, u8) -> u8) -> Result<(), MOS6502Error> {
        let a = self.fetch_pc_u8(mem)? as Address;
        let b = mem.get_u16(a)?;
        let addr = b + self.regs.y as Address;
        self.apply_addr(mem, addr, f)
        // XXX extra cycles?
    }

    pub fn dump(&self) {
        let mut flags = String::new();
        if (self.regs.fl & FLAG_N) != 0 { flags += "N"; } else { flags += "."; }
        if (self.regs.fl & FLAG_V) != 0 { flags += "V"; } else { flags += "."; }
        if (self.regs.fl & FLAG_1) != 0 { flags += "1"; } else { flags += "."; }
        if (self.regs.fl & FLAG_B) != 0 { flags += "B"; } else { flags += "."; }
        if (self.regs.fl & FLAG_D) != 0 { flags += "D"; } else { flags += "."; }
        if (self.regs.fl & FLAG_I) != 0 { flags += "I"; } else { flags += "."; }
        if (self.regs.fl & FLAG_Z) != 0 { flags += "Z"; } else { flags += "."; }
        if (self.regs.fl & FLAG_C) != 0 { flags += "C"; } else { flags += "."; }
        println!("a {:2x} x {:2x} y {:2x} fl {} ({:2x}) pc {:4x} sp {:4x}", self.regs.a, self.regs.x, self.regs.y, flags, self.regs.fl, self.regs.pc, self.regs.sp)
    }
}

fn do_asl(regs: &mut Registers, m: u8) -> u8 {
    let v = m << 1;
    regs.update_flags_nz(v);
    regs.set_or_clear_flag(FLAG_C, (m & 0x80) != 0);
    v
}

fn do_lsr(regs: &mut Registers, m: u8) -> u8 {
    let v = m >> 1;
    regs.update_flags_nz(v);
    regs.set_or_clear_flag(FLAG_C, (m & 1) != 0);
    v
}

fn do_ror(regs: &mut Registers, m: u8) -> u8 {
    let c = m & 1;
    let v = (c << 7) | (m >> 1);
    regs.update_flags_nz(v);
    regs.set_or_clear_flag(FLAG_C, c != 0);
    v
}

fn do_rol(regs: &mut Registers, m: u8) -> u8 {
    let c = m & 0x80;
    let v = (c >> 7) | (m << 1);
    regs.update_flags_nz(v);
    regs.set_or_clear_flag(FLAG_C, c != 0);
    v
}

fn do_sty(regs: &mut Registers, _m: u8) -> u8 {
    regs.y
}

fn do_stx(regs: &mut Registers, _m: u8) -> u8 {
    regs.x
}

fn do_sta(regs: &mut Registers, _m: u8) -> u8 {
    regs.a
}

fn do_dec(regs: &mut Registers, m: u8) -> u8 {
    let n = m.wrapping_sub(1);
    regs.update_flags_nz(n);
    n
}

fn do_inc(regs: &mut Registers, m: u8) -> u8 {
    let n = m.wrapping_add(1);
    regs.update_flags_nz(n);
    n
}

#[cfg(test)]
mod tests {

use super::*;

#[test]
fn test_dey() {
    let mut memory = Memory::new();
    for n in 0..3 {
        memory.set_u8(n, 0x88).unwrap(); // DEY
    }

    let mut cpu = MOS6502::new(&mut memory);

    // NZ
    cpu.regs.y = 0x80;
    cpu.execute().unwrap();
    assert_eq!(0x7f, cpu.regs.y);
    assert_eq!(FLAG_1, cpu.regs.fl);

    // Wrap around 255 -> 0
    cpu.regs.y = 0;
    cpu.execute().unwrap();
    assert_eq!(0xff, cpu.regs.y);
    assert_eq!(FLAG_1 | FLAG_N, cpu.regs.fl);
    cpu.dump();

    // Zero flag
    cpu.regs.y = 1;
    cpu.execute().unwrap();
    assert_eq!(0, cpu.regs.y);
    assert_eq!(FLAG_1 | FLAG_Z, cpu.regs.fl);
    cpu.dump();
}

#[test]
fn test_sty() {
    let mut memory = Memory::new();
    memory.set_u8(0, 0x84).unwrap();
    memory.set_u8(1, 0x0f).unwrap(); // STY 0f

    {
        let mut cpu = MOS6502::new(&mut memory);
        cpu.regs.y = 0x7f;
        assert_eq!(3, cpu.execute().unwrap());
    }
    assert_eq!(0x7f, memory.get_u8(0xf).unwrap());
    //cpu.dump();
}

}
