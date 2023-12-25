.data
    n: .word 10
    
.text
.globl __start

FUNCTION:
    addi t3, x0, 1
    addi t4, x0, 6
    addi t5, x0, 5
    addi sp, sp, -8
    sw x1, 4(sp)
    sw x10, 0(sp)
    srai x5, x10, 1
    bge x5, t3, L1
    addi x10, x0, 2
    addi sp, sp, 8
    jalr x0, 0(x1)
L1:
    srai x10, x10, 1
    jal x1, FUNCTION
    addi x6, x10, 0
    lw x10, 0(sp)
    lw x1, 4(sp)
    addi sp, sp, 8
    mul x6, x6, t5
    mul x10, x10, t4
    add x10, x10, x6
    addi x10, x10,4
    jalr x0, 0(x1)
__start:
    la   t0, n
    lw   x10, 0(t0)
    jal  x1,FUNCTION
    la   t0, n
    sw   x10, 4(t0)
    addi a0,x0,10
    ecall