# Block permutation matrices

For a permutation `w` of `Fin e`, `blockPerm w` permutes the blocks of
`Fin f × Fin e` and `permGL F w` is its permutation matrix. The lemmas
`permGL_mul` and `permGL_one` give the group law, and `permGL_conj` computes
conjugation by permuting rows and columns. The formula `permGL_swap`
identifies a block transposition with `pairGL hij swapU`, and
`permGL_conj_pairGL` transports a two-block element on blocks `i, j` to
blocks `w i, w j`. These identities compose the transposition calculations
along the inverse block cycle. [Cyclic compression](LevelZeroCycle.md)
