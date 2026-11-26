# Henniart's Harris datum with even real degree and weights at distance at least two

This module builds the datum of Harris (1998), Proposition 4.8, in Henniart's
globalization (Henniart 2000, §§3.3–3.6), with the two clauses of
`Harris.IsProposition48SpacedDatum` (module `HarrisProposition48SpacedData`). It states
and proves:

- `Harris.HarrisDatumCharacterRealizationSpacedStatement`: the published
  `HarrisDatumCharacterRealizationStatement` with the additional conclusion
  `IsRelativelySpaced E ξ`. On every paired-place configuration, for every normalized
  reciprocity family `e` and every continuous character `χ₀` of `F'ˣ`, there are `χ, χs, ξ`
  with the published `IsProposition48Datum e χ χs K₀ P Ps ξ`, with `ξ` relatively spaced
  over `E`, and with `χ = χ₀` on the units of `F'`.
- `HenniartHarrisDatumSpacedStatement`: the published `HenniartHarrisDatumStatement` with
  `Harris.IsProposition48SpacedDatum` in place of `IsProposition48Datum`. So the common
  base field also has even real degree, and the inducing character has weights at
  distance at least two.
- `HarrisDatum.harrisDatumCharacterRealizationSpaced_of_halfWeight`, a proof of the first
  statement from the published `CMHalfWeightCharacterStatement`.
- `henniartHarrisDatumSpaced`, a proof of the second statement. Only the standard axioms
  are used.

The published statements and their proofs are unchanged.

## The weights

The proof of `harrisDatumCharacterRealizationSpaced_of_halfWeight` is the published proof
of `harrisDatumCharacterRealization_of_halfWeight` (module
`HarrisDatumCharacterRealizationProof`) with the weights `2 · regularWeights` in place of
the published `regularWeights`. These are again anticyclotomic and distinct above the
embedding `τK` of the imaginary quadratic field. The published `cmRegularUnitPrescription`
then gives a character `X` of infinity type `σ ↦ m · 2 · regularWeights(σ)`. Its values are
even, and at distinct places above a place of `E` they differ (the published
`weights_ne_of_distinct`). Two distinct even integers differ by at least `2`. The weight-one
twist `ψ` has equal components at all places above a place of `E` (the published
`halfWeight_component_eq`). So `ξ = X ψ` is relatively spaced by
`isRelativelySpaced_of_weights`. The rest of the published proof is repeated without
change. The datum gets the published clauses, including relative regularity from the
published `isRelativelyRegular_of_weights`.

## Even real degree

The proof of `henniartHarrisDatumSpaced` repeats the published proof of
`henniartCommonBaseRealization` (module `HenniartCommonBaseRealizationProof`). The common
base field is the model field `modelField p Ω (cmModel p Ω) F.Carrier` of the CM Galois
model. The element `sqrtPos p Ω` lies in it by the published `mem_modelField_of_padic` and
`cmModelEmbedding_sqrtPos`. Its square is the positive rational `posSq p Ω`
(`sqrtPos_sq`, `posSq_pos`), which is not a square, because it is not a square in a larger
field (`posSq_not_isSquare`). So `hasEvenRealDegree_of_sq_pos` gives even real degree: the
real quadratic field `ℚ(√posSq)` lies in the maximal totally real subfield. This is
Henniart's real quadratic field `R` of 2001, §5.1. The datum characters on each
configuration then come from `harrisDatumCharacterRealizationSpaced_of_halfWeight` and the
published `cmHalfWeightCharacter`.

The children of the induction keep both clauses
(`Proposition48Problem.IsSpaced.of_auxiliaryMackeyChild` and
`Proposition48Problem.IsSpaced.withCorrectedCharacter`). The real quadratic field stays in
every base field because every child's base field is an extension of its parent's
(`IsMackeyChild`).

## Sources

- G. Henniart, *Une preuve simple des conjectures de Langlands pour `GL(n)` sur un corps
  `p`-adique*, Invent. Math. 139 (2000), §§3.3–3.6, as cited by the published
  `HenniartHarrisDatumStatement`. Registered `henniart-2000-simple-proof`, SHA256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
- G. Henniart, *Sur la conjecture de Langlands locale pour `GL_n`*, J. Théor. Nombres
  Bordeaux 13 (2001), §5.1 (printed p. 177). Registered
  `henniart-2001-langlands-locale-gln-jtnb`, SHA256
  `c9db009ee2f2e561d834b9e1ef07a8b27ff40d0edd19546d3351f38f39b2dac5`.
- M. Harris, *The local Langlands conjecture for `GL(n)` over a `p`-adic field, `n < p`*,
  Invent. Math. 134 (1998), §4, pp. 200–201, and Proposition 4.8. Registered
  `harris-1998-local-langlands`, SHA256
  `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
