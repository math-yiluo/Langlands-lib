# The lower root quotient for an adjacent transposition

For adjacent blocks `i` and `j = i + 1`, `blockSwap i j` exchanges their
indices. The identity `pairEmb_swap_conj` computes conjugation by
`pairGL hij swapU` by permuting rows and columns.

`thetaHom` sends `g ∈ J1` to the residue of its lower `(j, i)` block. The
target is the additive matrix group over `𝓀[F]`, written multiplicatively
in Lean. It is a homomorphism by `thetaFun_mul`. The diagonal blocks
reduce to the identity, and the remaining terms in the `(j, i)` block
of the product reduce to zero by the triangular residue conditions and
adjacency of `i` and `j`.

The kernel condition says that the `(j, i)` block also lies in the maximal
ideal. Then the row and column exchange preserves all defining conditions
of `J1`, by `swap_conj_mem_J1`. This kernel is contained in
`J1 ∩ s J1 s` for the transposition `s`, which lets compact averaging on
`π(s)v` for `J1`-fixed `v` use the finite quotient.
[Transposition step](LevelZeroSwapStep.md)
