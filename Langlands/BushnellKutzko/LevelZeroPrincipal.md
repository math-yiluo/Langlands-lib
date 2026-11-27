# Injectivity of diagonal compression for a level-zero type

For the standard principal order of period `e` and a uniformizer `ϖ`,
`aElt hϖ he` is the block diagonal matrix `diag(ϖ, 1, …, 1)` with `ϖ` on
block `0`. The product `piElt hϖ he = aElt hϖ he * permGL F (w0 e)`, where
`w0 e = cyc (e - 1)`, normalizes `U^1(𝔄)`. The normalization follows from the
entrywise conjugation formulas for `InOrd` and `InRad`.

The theorem `compressionMap_aElt_comp_eq_zero` concerns a representation
`ρ` of `U(𝔄)` that is trivial on `K = U^1(𝔄)` and satisfies the vanishing sums
of `LevelZeroCycle` on block `0`. If compression by `aElt` kills an
intertwining map `φ` from `ρ` to the restriction of a smooth representation
`π`, then `φ = 0`. This is the injectivity input needed from the principal
lemma BK93 (7.3.1) for the chosen contraction. Its proof is a direct
calculation on type intertwiners using the finite cuspidal sums. BK93 §7.4,
printed pp. 231–233 (PDF pp. 243–245), proves the principal lemma via
invertibility in the Hecke algebra. [Source details](LevelZeroNonmaximalTypeJacquetProof.md#source)

Use `piElt_mul_permGL` to write `aElt = Π * permGL (w0 e)⁻¹`, where
`Π = piElt hϖ he`. On `K`-fixed vectors, `compressionMap_mul_of_factor` and
`compressionMap_of_normalizes` identify compression by `aElt` with
compression by the inverse block cycle followed by `π(Π)`. The latter action
is invertible. The cyclic case `compressionMap_cyc_comp_eq_zero` then forces
`φ = 0`.
