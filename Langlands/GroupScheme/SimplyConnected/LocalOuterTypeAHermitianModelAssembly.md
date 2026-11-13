# Local outer type A Hermitian models from the unitary splitting statements

Author: Worker 166.

This module reduces the published `Langlands.GroupScheme.LocalOuterTypeAHermitianModelStatement`
to two published but unproved statements:

- `Langlands.GroupScheme.OuterTypeAUnitarySplitPresentationStatement`: over a field `K`
  with `UnitaryInvolutionSplitting K`, an affine, locally finite-type, simply connected,
  absolutely almost-simple group whose actual index has type `A_n` and whose actual star
  action moves some vertex has a presentation
  `HermitianMatrix.SchemeModel.Presentation K L J G` by a nonsingular Hermitian form `J`
  on `Fin (n + 1)` over a separable quadratic extension `L/K`;
- `Langlands.LocalUnitaryDivisionCommutativeStatement`: every nonarchimedean local field
  `K` satisfies `UnitaryDivisionCommutative K`.

It is part of Task 5973. Together with Worker 150's published reduction from
`LocalOuterTypeAHermitianModelStatement` to the task target
`LocalAnisotropicTypeAInnerStatement`, the task target then follows from these two
statements. This module proves neither of them.

## Statements

- `two_le_of_star_moves`: let `d` be actual Tits-index data of a group scheme over a
  field `K`. If `e : d.Vertex ≃ Fin n` and some absolute Galois element `σ` and vertex
  `a` have `d.star σ a ≠ a`, then `2 ≤ n`.
- `localOuterTypeAHermitianModel_of_unitarySplitting`: at every universe `u`,
  `OuterTypeAUnitarySplitPresentationStatement` and
  `LocalUnitaryDivisionCommutativeStatement` together imply
  `LocalOuterTypeAHermitianModelStatement`.

## Proofs

**`two_le_of_star_moves`.** If `n ≤ 1`, then `Fin n` has at most one element, so the
injective map `e` identifies `d.star σ a` with `a`. This contradicts the hypothesis.

**`localOuterTypeAHermitianModel_of_unitarySplitting`.** Fix a nonarchimedean local
field `K` and `G`, `d`, `n` with the hypotheses of `LocalOuterTypeAHermitianModelStatement`.

1. `LocalUnitaryDivisionCommutativeStatement` gives `UnitaryDivisionCommutative K`.
   Then `Langlands.Algebra.CentralSimple.unitaryDivisionSplitting` (module
   `Langlands/Algebra/CentralSimple/UnitaryDivisionSplitting`) gives
   `UnitaryInvolutionSplitting K`.
2. `OuterTypeAUnitarySplitPresentationStatement`, applied to `K`, this splitting
   property and the same hypotheses on `G`, gives a separable quadratic extension `L`, a
   Hermitian form `J` on `Fin (n + 1)` and a presentation `e : Presentation K L J G`.
3. The type-`A_n` numbering `d.Vertex ≃ Fin n` and the moved vertex give `2 ≤ n`
   (`two_le_of_star_moves`).
4. The published bridge
   `HermitianMatrix.SchemeModel.Presentation.exists_local_rootIso_of_card_eq_succ`
   (module `Langlands/GroupScheme/Examples/HermitianLocalPresentation`), applied to `e`,
   `2 ≤ n` and `Fintype.card (Fin (n + 1)) = n + 1`, gives a diagonal Hermitian form `H`
   on `Fin (n - 1)`, units `w` with `(w i : L) = H.weight i`, and an isomorphism
   `G ≅ HermitianRoot.SchemeModel.groupScheme K L H w hw`. This is the conclusion of
   `LocalOuterTypeAHermitianModelStatement` with the same `L`.

## Provenance

Internal. The module composes the published statements and theorems named above. The only
new mathematics is the counting step `2 ≤ n`. No external statement is transcribed.
