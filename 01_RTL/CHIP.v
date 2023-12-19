//----------------------------- DO NOT MODIFY THE I/O INTERFACE!! ------------------------------//
module CHIP #(                                                                                  //
    parameter BIT_W = 32                                                                        //
)(                                                                                              //
    // clock                                                                                    //
        input               i_clk,                                                              //
        input               i_rst_n,                                                            //
    // instruction memory                                                                       //
        input  [BIT_W-1:0]  i_IMEM_data,                                                        //
        output [BIT_W-1:0]  o_IMEM_addr,                                                        //
        output              o_IMEM_cen,                                                         //
    // data memory                                                                              //
        input               i_DMEM_stall,                                                       //
        input  [BIT_W-1:0]  i_DMEM_rdata,                                                       //
        output              o_DMEM_cen,                                                         //
        output              o_DMEM_wen,                                                         //
        output [BIT_W-1:0]  o_DMEM_addr,                                                        //
        output [BIT_W-1:0]  o_DMEM_wdata,                                                       //
    // finnish procedure                                                                        //
        output              o_finish,                                                           //
    // cache                                                                                    //
        input               i_cache_finish,                                                     //
        output              o_proc_finish                                                       //
);                                                                                              //
//----------------------------- DO NOT MODIFY THE I/O INTERFACE!! ------------------------------//

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Parameters
// ------------------------------------------------------------------------------------------------------------------------------------------------------



//OP code
    // R-type
    parameter R_TYPE   = 7'b0110011;
    // I-type
    parameter IMM_OPS  = 7'b0010011;
    parameter LW    = 7'b0000011;
    // B-type
    parameter B_TYPE   = 7'b1100011;    
    // S-type
    parameter SW    = 7'b0100011;
    // J-type
    parameter JAL   = 7'b1101111;
    parameter JALR  = 7'b1100111;
    // U-type
    parameter AUIPC = 7'b0010111;

    parameter ECALL = 7'b1110011;

    //====== funct3 ======
    parameter ADD_FUNC3  = 3'b000;
    parameter SUB_FUNC3  = 3'b000;
    parameter XOR_FUNC3  = 3'b100;
    parameter MUL_FUNC3  = 3'b000;

    parameter ADDI_FUNC3 = 3'b000;
    parameter SLTI_FUNC3 = 3'b010;
    parameter SLLI_FUNC3 = 3'b001;
    parameter SRAI_FUNC3 = 3'b101;

    parameter BEQ_FUNC3   = 3'b000;
    parameter BNE_FUNC3   = 3'b001;
    parameter BLT_FUNC3   = 3'b100;
    parameter BGE_FUNC3   = 3'b101;

    //====== funct7 ======
    parameter ADD_FUNC7 = 7'b0000000;
    parameter SUB_FUNC7 = 7'b0100000;
    parameter XOR_FUNC7 = 7'b0000000;
    parameter MUL_FUNC7 = 7'b0000001;

    parameter I_MUL  = 3'd6;

    //===== FSM parameter ====
    parameter S_IDLE = 2'd0;
    parameter S_EX = 2'd1;
    parameter S_MEM = 2'd2;
    parameter S_MUL = 2'd3;


    // TODO: any declaration

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Wires and Registers
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    
    // TODO: any declaration
        reg [BIT_W-1:0] PC=0, next_PC;
        reg mem_cen, mem_wen;
        reg [BIT_W-1:0] mem_addr, mem_wdata, mem_rdata;
        reg mem_stall;

        reg reg_wen;
        reg [BIT_W-1:0] rs1, rs2, rd, wdata, rdata1, rdata2;

        reg alu_valid, alu_done;
        reg [BIT_W-1:0] alu_A, alu_B;
        reg [2:0] alu_op;
        reg [BIT_W-1:0] alu_result;
        reg [BIT_W-1:0] final_result;

        reg [BIT_W-1:0] instruction;

        reg is_finish, is_finish_nxt;

        reg [1: 0] state = S_EX;
        reg [1: 0] state_nxt;

        reg [6: 0] op_code;
        reg [2: 0] funct3;
        reg [6: 0] funct7;
        reg [BIT_W-1:0] imm;

        wire [BIT_W-1:0] rdata1_w, rdata2_w, alu_result_w;
        wire alu_done_w;
        wire cache_done_w;

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Continuous Assignment
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: any wire assignment

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Submoddules
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: Reg_file wire connection
    Reg_file reg0(               
        .i_clk  (i_clk),             
        .i_rst_n(i_rst_n),         
        .wen    (reg_wen),          
        .rs1    (rs1),                
        .rs2    (rs2),                
        .rd     (rd),                 
        .wdata  (wdata),             
        .rdata1 (rdata1_w),           
        .rdata2 (rdata2_w)
    );

    MULDIV_unit muldiv0(
        .i_clk(i_clk),
        .i_rst_n(i_rst_n),
        .i_valid(alu_valid),
        .i_A(alu_A),
        .i_B(alu_B),
        .i_inst(alu_op),
        .o_data(alu_result_w),
        .o_done(alu_done_w)
    );

    assign o_IMEM_addr = PC;
    assign o_IMEM_cen = 1'b1;

    assign o_DMEM_cen = mem_cen;
    assign o_DMEM_wen = mem_wen;
    assign o_DMEM_addr = mem_addr;
    assign o_DMEM_wdata = mem_wdata;


    assign o_finish = is_finish;

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Always Blocks
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    

    always @(*) begin

        instruction = i_IMEM_data;
        mem_rdata = i_DMEM_rdata;
        mem_stall = i_DMEM_stall;
    
        op_code = instruction[6:0];
        funct3 = instruction[14:12];
        funct7 = instruction[31:25];
        rs1 = instruction[19:15];
        rs2 = instruction[24:20];
        rd = instruction[11:7];

        next_PC = PC + 4;
        is_finish_nxt = 0;
        mem_cen = 0;
        mem_wen = 0;
        mem_addr = 0;
        mem_wdata = 0;
        reg_wen = 0;
        alu_valid = 0;
        alu_A = 0;
        alu_B = 0;
        alu_op = 0;

        alu_result = alu_result_w;
        alu_done = alu_done_w;
        rdata1 = rdata1_w;
        rdata2 = rdata2_w;


        case (op_code)
            ECALL: begin
                is_finish_nxt = 1;
                state_nxt = S_IDLE;
            end
            AUIPC: begin
                reg_wen = 1;
                state_nxt = S_EX;
                imm[31:12] = instruction[31:12];
                imm[11:0] = 0;
                wdata = PC + imm;
            end
            JAL: begin
                reg_wen = 1;
                state_nxt = S_EX;
                imm[20:0] = {instruction[31], instruction[19:12], instruction[20], instruction[30:21], 1'b0};
                wdata = PC + 4;
                next_PC = PC + imm;
            end
            JALR: begin
                reg_wen = 1;
                state_nxt = S_EX;
                imm[11:0] = instruction[31:20];
                wdata = PC + 4;
                next_PC = $signed(rdata1) + $signed(imm);
            end
            R_TYPE: begin
                reg_wen = 1;
                case ({funct3, funct7})
                    {ADD_FUNC3, ADD_FUNC7}: begin
                        state_nxt = S_EX;
                        final_result = $signed(rdata1) + $signed(rdata2);
                    end
                    {SUB_FUNC3, SUB_FUNC7}: begin
                        state_nxt = S_EX;
                        final_result = $signed(rdata1) - $signed(rdata2);
                    end
                    {XOR_FUNC3, XOR_FUNC7}: begin
                        state_nxt = S_EX;
                        final_result = rdata1 ^ rdata2;
                    end
                    {MUL_FUNC3, MUL_FUNC7}: begin
                        if (alu_done && state == S_MUL) begin
                            state_nxt = S_EX;
                            reg_wen = 1;
                        end
                        else begin
                            state_nxt = S_MUL;
                            reg_wen = 0;
                        end
                        alu_valid = 1;
                        alu_A = rdata1;
                        alu_B = rdata2;
                        alu_op = I_MUL;
                        final_result = alu_result;
                    end
                    default: begin
                        alu_valid = 0;
                        alu_A = 0;
                        alu_B = 0;
                        alu_op = 0;
                        state_nxt = S_EX;
                    end
                endcase
                wdata = final_result;
            end
            IMM_OPS: begin
                state_nxt = S_EX;
                reg_wen = 1;
                imm[11:0] = instruction[31:20];
                case (funct3)
                    ADDI_FUNC3: begin
                        final_result = $signed(rdata1) + $signed(imm);
                    end
                    SLTI_FUNC3: begin
                        final_result = ($signed(rdata1) < $signed(imm)) ? 1 : 0;
                    end
                    SLLI_FUNC3: begin
                        final_result = rdata1 << imm;
                    end
                    SRAI_FUNC3: begin
                        final_result = $signed(rdata1) >> imm;
                    end
                    default: begin
                        alu_valid = 0;
                        alu_A = 0;
                        alu_B = 0;
                        alu_op = 0;
                    end
                endcase
                wdata = final_result;
            end
            LW: begin
                state_nxt = S_EX;
                wdata = mem_rdata;
                mem_cen = 1;
                mem_addr = $signed(rdata1) + $signed(instruction[31:20]);
                mem_wen = 0;
                reg_wen = 1;
            end
            SW: begin
                state_nxt = S_EX;
                mem_cen = 1;
                mem_addr = $signed(rdata1) + $signed(instruction[31:25]);
                mem_wen = 1;
                mem_wdata = rdata2;
                reg_wen = 0;
            end
            B_TYPE: begin
                state_nxt = S_EX;
                imm[12:0] = {instruction[31], instruction[7], instruction[30:25], instruction[11:8], 1'b0};
                case (funct3)
                    BEQ_FUNC3: begin
                        if (rdata1 == rdata2) begin
                            next_PC = PC + $signed(imm[12:0]);
                        end
                        else begin
                            next_PC = PC + 4;
                        end
                    end
                    BNE_FUNC3: begin
                        if (rdata1 != rdata2) begin
                            next_PC = PC + $signed(imm[12:0]);
                        end
                        else begin
                            next_PC = PC + 4;
                        end
                    end
                    BLT_FUNC3: begin
                        if ($signed(rdata1) < $signed(rdata2)) begin
                            next_PC = PC + $signed(imm[12:0]);
                        end
                        else begin
                            next_PC = PC + 4;
                        end
                    end
                    BGE_FUNC3: begin
                        if ($signed(rdata1) >= $signed(rdata2)) begin
                            next_PC = PC + $signed(imm[12:0]);
                        end
                        else begin
                            next_PC = PC + 4;
                        end
                    end

                    default: begin
                        alu_valid = 0;
                        alu_A = 0;
                        alu_B = 0;
                        alu_op = 0;
                    end
                endcase
            end
            default: begin
                alu_valid = 0;
                alu_A = 0;
                alu_B = 0;
                alu_op = 0;
                state_nxt = S_EX;
            end
        endcase
        $display("instruction: %d", instruction);
        $display("PC: %d", PC);
        
        if (state != S_EX) begin
            next_PC = PC;
        end
        else begin
            next_PC = PC + 4;
        end 
        
    end
    // Todo: any combinational/sequential circuit

    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            PC <= 32'h00010000; // Do not modify this value!!!
            is_finish <= 0;
            state <= state_nxt;
        end
        if (mem_stall) begin
            PC <= PC;
            is_finish <= is_finish_nxt;
            state <= state_nxt;

        end
        else begin
            PC <= next_PC;
            is_finish <= is_finish_nxt;
            state <= state_nxt;
        end
    end
endmodule

module Reg_file(i_clk, i_rst_n, wen, rs1, rs2, rd, wdata, rdata1, rdata2);
   
    parameter BITS = 32;
    parameter word_depth = 32;
    parameter addr_width = 5; // 2^addr_width >= word_depth
    
    input i_clk, i_rst_n, wen; // wen: 0:read | 1:write
    input [BITS-1:0] wdata;
    input [addr_width-1:0] rs1, rs2, rd;

    output [BITS-1:0] rdata1, rdata2;

    reg [BITS-1:0] mem [0:word_depth-1];
    reg [BITS-1:0] mem_nxt [0:word_depth-1];

    integer i;

    assign rdata1 = mem[rs1];
    assign rdata2 = mem[rs2];

    always @(*) begin
        for (i=0; i<word_depth; i=i+1)
            mem_nxt[i] = (wen && (rd == i)) ? wdata : mem[i];
    end

    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1) begin
                case(i)
                    32'd2: mem[i] <= 32'hbffffff0;
                    32'd3: mem[i] <= 32'h10008000;
                    default: mem[i] <= 32'h0;
                endcase
            end
        end
        else begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1)
                mem[i] <= mem_nxt[i];
        end       
    end
endmodule


module Cache#(
        parameter BIT_W = 32,
        parameter ADDR_W = 32
    )(
        input i_clk,
        input i_rst_n,
        // processor interface
            input i_proc_cen,
            input i_proc_wen,
            input [ADDR_W-1:0] i_proc_addr,
            input [BIT_W-1:0]  i_proc_wdata,
            output [BIT_W-1:0] o_proc_rdata,
            output o_proc_stall,
            input i_proc_finish,
            output o_cache_finish,
        // memory interface
            output o_mem_cen,
            output o_mem_wen,
            output [ADDR_W-1:0] o_mem_addr,
            output [BIT_W*4-1:0]  o_mem_wdata,
            input [BIT_W*4-1:0] i_mem_rdata,
            input i_mem_stall,
            output o_cache_available,
        // others
        input  [ADDR_W-1: 0] i_offset
    );

    assign o_cache_available = 0; // change this value to 1 if the cache is implemented

    //------------------------------------------//
    //          default connection              //
    assign o_mem_cen = i_proc_cen;              //
    assign o_mem_wen = i_proc_wen;              //
    assign o_mem_addr = i_proc_addr;            //
    assign o_mem_wdata = i_proc_wdata;          //
    assign o_proc_rdata = i_mem_rdata[0+:BIT_W];//
    assign o_proc_stall = i_mem_stall;          //
    //------------------------------------------//

    // Todo: BONUS

endmodule
module MULDIV_unit #(
    parameter DATA_W = 32
)
(
    input                       i_clk,   // clock
    input                       i_rst_n, // reset

    input                       i_valid, // input valid signal
    input [DATA_W - 1 : 0]      i_A,     // input operand A
    input [DATA_W - 1 : 0]      i_B,     // input operand B
    input [         2 : 0]      i_inst,  // instruction

    output [2*DATA_W - 1 : 0]   o_data,  // output value
    output                      o_done   // output valid signal
);
// Do not Modify the above part !!!
/*
    initial begin
            $dumpfile ("ALU.vcd");
            $dumpvars (0, ALU);
            #1;
        end*/

// Parameters
    // ======== choose your FSM style ==========
    // 1. FSM based on operation cycles
    parameter S_IDLE           = 2'd0;
    parameter S_ONE_CYCLE_OP   = 2'd1;
    parameter S_MULTI_CYCLE_OP = 2'd2;
    // 2. FSM based on operation modes
    parameter S_ADD  = 3'd0; //OK
    parameter S_SUB  = 3'd1; //OK
    parameter S_AND  = 3'd2; //OK
    parameter S_OR   = 3'd3; //OK
    parameter S_SLT  = 3'd4; //OK
    parameter S_SRA  = 3'd5; //OK
    parameter S_MUL  = 3'd6; //OK
    parameter S_DIV  = 3'd7;

    parameter SMALLEST_NEG = 32'h80000000;
    parameter LARGEST_POS = 32'h7FFFFFFF;

// Wires & Regs
    // Todo
    // state
    reg  [         1: 0] state, state_nxt; // remember to expand the bit width if you want to add more states!
    // load input
    reg  [  DATA_W-1: 0] operand_a, operand_a_nxt;
    reg  [  DATA_W-1: 0] operand_b, operand_b_nxt;
    reg  [2 * DATA_W-1: 0] alu_temp;
    reg  [         2: 0] inst, inst_nxt;

    reg [2*DATA_W-1 : 0] o_curr;
    reg [2*DATA_W-1 : 0] o_data_nxt;
    
    reg [4 :0] counter, counter_nxt;
    reg o_done_nxt;
    reg ready;
    reg toDivide;


// Wire Assignments
    // Todo
    assign o_data = o_curr;
    assign o_done = ready;

// Always Combination
    // load input
    always @(*) begin
        if (i_valid) begin
            operand_a_nxt = i_A;
            operand_b_nxt = i_B;
            inst_nxt      = i_inst;
        end
        else begin
            operand_a_nxt = operand_a;
            operand_b_nxt = operand_b;
            inst_nxt      = inst;
        end
    end
    //FSM
    always @(*) begin
        case(state)
            S_IDLE           : if (!i_valid) begin
                                    state_nxt = S_IDLE;
                                end
                                else begin
                                    case (i_inst)
                                        S_ADD : state_nxt = S_ONE_CYCLE_OP;
                                        S_SUB : state_nxt = S_ONE_CYCLE_OP;
                                        S_AND : state_nxt = S_ONE_CYCLE_OP;
                                        S_OR  : state_nxt = S_ONE_CYCLE_OP;
                                        S_SLT : state_nxt = S_ONE_CYCLE_OP;
                                        S_SRA : state_nxt = S_ONE_CYCLE_OP;
                                        S_MUL : state_nxt = S_MULTI_CYCLE_OP;
                                        S_DIV : state_nxt = S_MULTI_CYCLE_OP;
                                        default : state_nxt = S_IDLE;
                                    endcase
                                end
            S_ONE_CYCLE_OP   : state_nxt = S_IDLE;
            S_MULTI_CYCLE_OP : if (counter == 5'd31) begin
                                    state_nxt = S_IDLE;
                                end
                                else begin
                                    state_nxt = S_MULTI_CYCLE_OP;
                                end
            default          : state_nxt = S_IDLE;
        endcase
    end
    //Counter
    always @(*) begin
        if (state == S_MULTI_CYCLE_OP) begin
            counter_nxt = counter + 1;
        end
        else begin
            counter_nxt = 0;
        end
    end 

    // Todo: ALU output
    always @(*) begin
        case (i_inst)
            S_ADD : begin
                alu_temp = operand_a + operand_b;
                if (alu_temp[31] == 0 && operand_a[31] == 1 && operand_b[31] == 1) begin
                    //negative overflow
                    o_data_nxt = SMALLEST_NEG; 
                    o_data_nxt[63:32] = {32{1'b0}};
                end
                else if (alu_temp[31] != 0 && operand_a[31] == 0 && operand_b[31] == 0) begin
                    //positive overflow
                    o_data_nxt = LARGEST_POS; 
                    o_data_nxt[63:32] = {32{1'b0}};
                end
                else begin
                    o_data_nxt = alu_temp[31:0];
                end
            end
            S_SUB : begin
                alu_temp = operand_a - operand_b;
                if (operand_a[31] != operand_b[31]) begin
                    if (operand_b[31] == 0 && alu_temp[31] != 1) begin
                        //negative overflow neg - pos = neg
                        o_data_nxt = SMALLEST_NEG; 
                        o_data_nxt[63:32] = {32{1'b0}};
                    end
                    else if (operand_a[31] == 0 && alu_temp[31] != 0) begin
                        //positive overflow pos - neg = pos
                        o_data_nxt = LARGEST_POS; 
                        o_data_nxt[63:32] = {32{1'b0}};
                    end
                    else begin
                        o_data_nxt = alu_temp[31:0];
                    end
                end
                else begin
                    o_data_nxt = alu_temp[31:0];
                end
            end
            S_AND : begin
                o_data_nxt = operand_a & operand_b;
            end
            S_OR  : begin
                o_data_nxt = operand_a | operand_b;
            end
            S_SLT : begin
                if(operand_a[31] == 1 && operand_b[31] != 1) begin
                    o_data_nxt = 1;
                end
                else if(operand_a[31] != 1 && operand_b[31] == 1) begin
                    o_data_nxt = 0;
                end
                else begin
                    o_data_nxt = operand_a < operand_b;
                end
            end
            S_SRA : begin
                alu_temp = $signed(operand_a) >> operand_b;
                o_data_nxt = alu_temp[31:0];
            end
            S_MUL : begin
                        alu_temp = o_curr[63:32] + operand_a;
                        if (i_valid && state == S_IDLE) begin
                            o_data_nxt = {{32{1'b0}}, operand_b_nxt};
                        end
                        else begin
                            if(o_curr[0] == 1) begin
                                o_data_nxt = {alu_temp[32:0], o_curr[31:1]};
                            end
                            else begin
                                o_data_nxt = o_curr[63:1];
                            end
                        end
            end
            S_DIV : begin
                        alu_temp = o_curr[63:32] - operand_b;
                        if (i_valid && state == S_IDLE) begin
                            o_data_nxt = {{31{1'b0}}, operand_a_nxt, {1'b0}};
                        end
                        else begin
                            toDivide = ((o_curr[63:32] >= operand_b) ? 1'b1 : 1'b0);
                            if (counter == 5'd31) begin
                                if (toDivide) begin
                                    o_data_nxt = {alu_temp, o_curr[30:0], {1'b1}};
                                end
                                else begin
                                    o_data_nxt = {o_curr[63:32], o_curr[30:0], {1'b0}};
                                end
                            end
                            else begin
                                if (toDivide) begin
                                    o_data_nxt = {alu_temp, o_curr[31:0], {1'b1}};
                                end
                                else begin
                                o_data_nxt = {o_curr, {1'b0}};
                                end
                            end
                        end
            end
            default : begin
                o_data_nxt = 0;
            end
        endcase
    end

    
    // Todo: output valid signal
    always @(*) begin
        case (state)
            S_IDLE : begin 
                o_done_nxt = 0; 
                end
            S_ONE_CYCLE_OP : begin 
                o_done_nxt = 1; 
                end
            S_MULTI_CYCLE_OP : if (counter == 5'd31) begin
                                    o_done_nxt = 1;
                                end
                                else begin
                                    o_done_nxt = 0;
                                end
            default : begin
                o_done_nxt = 0;
            end
        endcase
    end

    // Todo: Sequential always block
    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            state       <= S_IDLE;
            operand_a   <= 0;
            operand_b   <= 0;
            inst        <= 0;
            counter     <= 0;
        end
        else begin
            state       <= state_nxt;
            operand_a   <= operand_a_nxt;
            operand_b   <= operand_b_nxt;
            inst        <= inst_nxt;
            counter     <= counter_nxt;
            o_curr      <= o_data_nxt;
            ready     <= o_done_nxt;
        end
    end

endmodule
