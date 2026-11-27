# Two-block embeddings for the standard principal order

For distinct blocks `i` and `j`, `pairEquiv` identifies
`(Fin f ⊕ Fin f) ⊕ PairRest e f i j` with `Fin f × Fin e`, with the first two
summands going to blocks `i` and `j`. The map `pairEmb hij M` places a
`2 × 2` block matrix `M` on those two blocks and acts as the identity
elsewhere. It respects multiplication and identity by `pairEmb_mul` and
`pairEmb_one`. The induced homomorphism on units is `pairGL hij`.

The lemmas `pairEmb_ll`, `pairEmb_lr`, `pairEmb_rl`, `pairEmb_rr`,
`pairEmb_rest_left` and `pairEmb_rest_right` compute the entries in each
part of the matrix. They allow the computations for an adjacent
transposition to take place on just two blocks.
[Transposition step](LevelZeroSwapStep.md)
