# The first-block parabolic and its Iwahori factorization

The index set `Fin f × Fin e` splits into `TopIx f he` for the first block and
`RstIx f he` for its complement. The maps `coarseEquiv` and `coarseReindex`
implement this splitting. In these coordinates, `coarseN` is the upper
unipotent radical (the image of `upperHom`), `coarseM` is the block diagonal
Levi subgroup (the image of `leviHom`), and `coarseNbar` is the lower
unipotent radical (the image of `lowerHom`). The identity
`coarseM_le_normalizer` records the Levi action on `coarseN`.

`coarse_factor` writes each `x ∈ U(𝔄)` as `l * m * u`, with
`l ∈ U^1(𝔄) ∩ coarseNbar`, `m ∈ U(𝔄) ∩ coarseM` and
`u ∈ U^1(𝔄) ∩ coarseN`. The upper left blocks `A` of `x` and `A'` of `x⁻¹`
satisfy `A A' ≡ 1` modulo the maximal ideal because the upper right block of
`x` lies in that ideal. This gives an integral inverse for `A` via
`exists_isIntGL_of_sub_one`. Block LU decomposition
(`Matrix.fromBlocks_eq_of_invertible₁₁`) gives the factorization with the
required bounds on the off-diagonal entries. For `K = U^1(𝔄)`,
`coarse_J1_factor` restricts it to `K`, since `l⁻¹ * x * u⁻¹` belongs to `K`
when `x` does.

`coarse_isWeakIwahoriContraction` shows that `aElt = diag(ϖ, 1, …, 1)` is a
weak Iwahori contraction for `K` relative to `(coarseN, coarseM, coarseNbar)`.
Conjugation by `aElt` multiplies the upper right block by `ϖ`, conjugation by
its inverse multiplies the lower left block by `ϖ`, and `aElt` commutes with
the Levi. In `coarse_exhaust`, a large enough power of `aElt` carries an
element of `coarseN` into `K`. The proof takes the maximum of the exponents
that carry each entry of the upper right block into the maximal ideal.
These facts supply the matrix hypotheses for the contraction argument.
[Compression criterion](TypeJacquetCompression.md)
