# Actual second-rectangle support at Levi elements

This derived internal lemma applies `exists_blockSum_rectangular_support`
to the actual factorization `matrix_levi_diagonalBlocks`. The matrix is
the one in Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg
convolutions* (1983), §4.10(2), printed p. 419 (registered source
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`).
The source does not separately state this auxiliary compact-support
formulation.

Fix any p-adic field, a unitary additive character, positive block sizes
`m 0 + 1` and `m 1 + 1` with total `t + 1`, complementary dimensions
`j,k : ℕ`, and `r = t + (j + k + 1)`. Let `π` be a smooth complex
representation of `GL_(r+1)`, `ell` any supplied Whittaker functional, and
`W` any coefficient in its coefficient model. No irreducibility,
nonzero-functional or genericity hypothesis is imposed.

`IsLeviSecondRectangularSupport` says that `C` is compact and contains
`y.submatrix Fin.rev Fin.rev * (b 1).val` whenever `W` is nonzero at
`matrix h hr (leviEmbedding b * c) x y`, for every actual Levi element
`b`, right factor `c ∈ integralOpen F t`, and rectangular coordinates
`x,y`. Thus `exists_levi_second_rectangular_support` gives one set uniform
in both Levi blocks, the first rectangle and every right integral factor.

The generic integral-subgroup lemmas check both matrices and inverses.
The rank-transport helper uses equality elimination only. The final proof
uses the leading block `unequalRankMatrix j 0 (b 1) (y.rev * b 1)`;
the complementary invertible block has rank `k + m 0 + 1`. It absorbs
the column-alignment permutation and appended right integral factor into
the integral factor in the block-sum theorem, then applies its compact
support conclusion to the coefficient nonvanishing hypothesis. All
complementary dimensions, including zero, remain allowed. This lemma
supplies compact support only; rectangle volumes and integrability are
separate obligations.
