# Tools for small growth bounds on principal series

## Definitions

- `SmallGrowth n χ`: there is a subspace `E` of the `U(n)`-finite functions of
  `principalSeries ℂ n χ` that is nonzero, finite-dimensional and stable under
  `principalSeriesRep ℂ n χ k` for all `k ∈ U(n)`, and a real `C` with
  `finrank (filtrationSpan (principalSeriesLie ℂ n χ) d E) ≤ C (d + 1)^{n(n-1)-1}` for all `d`.
  For `χ = complexPositionCharacter ds'` this is, after unfolding the abbreviations
  `complexStandardModule`, `complexStandardRep`, `complexStandardLie`, exactly the conclusion of
  `ComplexLinkedSmallGrowthStatement` (module `ComplexLinkedLanglandsQuotientGrowth`).
- `levelIn W N`: a subspace `W N` of functions pulled back to the `U(n)`-finite functions.

## Results

- For an increasing sequence `W N` of subspaces of functions such that right derivatives map
  `W N` into `W (N + 1)`: `lie_mem_levelIn`, `degreeOne_mem_levelIn`,
  `degreeFiltration_mem_levelIn` (elements of degree `≤ d` of `U(ℂ ⊗_ℝ 𝔤𝔩_n(ℂ))` raise the level
  by at most `d`), `filtrationSpan_le_levelIn` (`E ⊆ W 0` implies `U_d(𝔤) · E ⊆ W d`) and
  `finrank_filtrationSpan_le` (`dim U_d(𝔤) · E ≤ dim W d` when `W d` is finite-dimensional).
- `smallGrowth_of_intertwine`: `SmallGrowth n χ₁` implies `SmallGrowth n χ₂` along an injective
  linear map of the `U(n)`-finite functions intertwining `principalSeriesRep` and
  `principalSeriesLie`; the image of `E` works, and
  `U_d(𝔤) · A E ⊆ A (U_d(𝔤) · E)` by the Library theorem `envelopingAction_intertwine`
  (module `RealLargeLanglandsQuotientReduction`), which extends the intertwining property from
  the Lie algebra to its universal enveloping algebra.

## Provenance

Internal infrastructure of Task 7064 for the growth bound `ComplexLinkedSmallGrowthStatement`,
one of the two growth statements of the dimension-count route to
`ComplexLinkedLanglandsQuotientNotLargeStatement` in the Library module
`ComplexLinkedLanglandsQuotientGrowth`; see `ComplexLinkedSmallGrowthProof.md` for how the pieces
fit together. This route is an independent internal proof, not taken from the literature. The
module introduces no statement from the literature, and all its results are proved here.
