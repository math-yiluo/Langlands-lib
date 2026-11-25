# The span of the level products

`levelSpan h b dτ` is the complex span of all functions `levelProduct h b dτ A`.

## Definitions

- `toMat`, `ofMat`: matrices from and to their entry vectors `Fin n × Fin n → ℂ`.
- `detDegree n h b = ∑_m (h_m + b_m) n`.
- `levelWeight h b dτ g = ∏_m gramPart m g`: the Gram weight common to all level products.
- `weightMap`: multiplication of a function of the entries by the Gram weight.
- `selectMatrices`: all level matrices equal to `tailSelect m`.

## Results

- `levelDet_mem_degLE`, `detPart_mem_degLE`: as functions of the entries, `levelDet m A` has
  degree `≤ n` and `detPart m A` degree `≤ (h_m + b_m) n` (`RealPolynomialFunctions.degLE`).
- `levelProduct_eq_weightMap`, `levelSpan_le_map`: every level product is the Gram weight times
  a polynomial of degree `≤ detDegree n h b` in the entries; hence
  `levelSpan_finiteDimensional`.
- `rightTranslation_mem_levelSpan`: the span is stable under right translation by `U(n)`
  (`levelProduct_mul_unitary`).
- `levelProduct_tailSelect_one`, `levelSpan_ne_bot`: the level product of `selectMatrices`
  takes the value `1` at the identity, so the span is nonzero.
- `levelSpan_le_kFiniteFunctions`: under the telescoping hypotheses of
  `levelProduct_mem_principalSeries`, the span lies in the `U(n)`-finite functions of
  `principalSeries ℂ n χ` (its `U(n)`-translates of an element span a subspace of the
  finite-dimensional `levelSpan`).

## Provenance

Internal infrastructure for the growth bound `ComplexLinkedSmallGrowthStatement`,
one of the two growth statements of the dimension-count route to
`ComplexLinkedLanglandsQuotientNotLargeStatement` in the Library module
`ComplexLinkedLanglandsQuotientGrowth`; see `ComplexLinkedSmallGrowthProof.md` for how the pieces
fit together. This route is an independent internal proof, not taken from the literature. The
module introduces no statement from the literature, and all its results are proved here.
