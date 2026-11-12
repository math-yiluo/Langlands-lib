# The completion of a regular local ring is regular

This helper module for the proof of
`Langlands.CommutativeAlgebra.FiniteTypeIntGRingStatement` contains one
theorem, in the namespace `Langlands.CommutativeAlgebra.FiniteTypeIntGRing`.

## Statement

`isRegularLocalRing_adicCompletion R`: for every regular local ring `R` (in an
arbitrary universe), the adic completion `AdicCompletion (maximalIdeal R) R`
of `R` at its maximal ideal is a regular local ring.

This is the standard fact that a Noetherian local ring is regular if and only
if its completion is (here only the direction from `R` to its completion is
proved). The module is internal to the project's proof and does not follow a
specific reference.

## Proof

Write `Â` for the completion and `𝔪`, `𝔪̂` for the maximal ideals.

- `Â` is Noetherian by `AdicCompletion.isNoetherianRing_of_isNoetherianRing`,
  imported from the Library module
  `Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing`.
  Mathlib makes `Â` a local ring.
- By Mathlib's `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le` it suffices
  that the minimal number of generators of `𝔪̂` is at most `dim Â`.
- Mathlib's `AdicCompletion.spanFinrank_maximalIdeal_eq` says that `𝔪̂` and
  `𝔪` need the same number of generators, and regularity of `R` makes this
  number equal to `dim R` (`IsRegularLocalRing.spanFinrank_maximalIdeal`).
- Both dimensions are heights of maximal ideals
  (`maximalIdeal_height_eq_ringKrullDim`). Mathlib provides that `Â` is flat
  over `R`, so the extension `R → Â` has going down. The maximal ideal `𝔪̂`
  lies over `𝔪`, and Mathlib's
  `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` gives
  `ht 𝔪̂ = ht 𝔪 + (height of the image of 𝔪̂ in Â ⧸ 𝔪 Â)`.
  In particular `ht 𝔪 ≤ ht 𝔪̂`, which is the required inequality.
