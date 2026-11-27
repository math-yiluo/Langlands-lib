# Outer type A groups as special unitary groups from the Tits cocycle

Module `Langlands.GroupScheme.SimplyConnected.OuterTypeAUnitaryAlgebraReduction`, namespace
`Langlands.GroupScheme.OuterTypeAUnitaryAlgebra`.

This internal module proves that the published proposition
`SpecialLinearTitsCocycleStatement` implies the published proposition
`OuterTypeAUnitaryAlgebraPresentationStatement`, in the same universe. The Tits cocycle
proposition is an explicit premise here.

## Coefficients

For a cover point `a : Z ⟶ cover K M` (that is, a morphism to `Spec M` over `Spec K`),
`coefficientHom a : M →ₐ[K] Γ(Z)` (def) is the published `coefficients a`, a `K`-algebra map
by `OuterTypeAHermitian.coefficients_algebraMap`. `coefficientHom_naturality`: for
`t : W ⟶ Z`, `coefficientHom (t ≫ a)` is `coefficientHom a` followed by the global-section
map of `t`. `coefficientHom_coverAut`: `coefficientHom (a ≫ coverAut K M σ)` is
`coefficientHom a ∘ σ`.

## Local isomorphisms

Fix `M/K` finite Galois, an intermediate field `F` that is separable quadratic over `K` (the
section also assumes `[Normal K F]`, which holds for quadratic extensions), and
`c : UnitaryTwistedChart.Cocycle F (Fin (n + 1))` (module
`Langlands.LinearAlgebra.UnitaryTwistedChart`). Write `B = c.Alg` and `τ = c.involution`, and
`SU(B, τ) = UnitaryAlgebra.groupScheme F τ` (module
`Langlands.GroupScheme.Examples.UnitaryAlgebraGroupScheme`). Let `E` be a local isomorphism
from `SL_(n+1)` to a group scheme `G` over `cover K M`.

- `localEquiv c E a` (def): the composite of `UnitaryAlgebra.pointsEquiv`, the chart
  `c.suChart (coefficientHom a) : SU(B, τ)(Γ(Z)) ≃* SL_(n+1)(Γ(Z))`, the inverse of the
  published `SpecialLinear.pointsEquiv`, and `E.toFun a`. `localEquiv_apply` unfolds it.
- `localEquiv_naturality`: naturality in the test scheme, from
  `UnitaryAlgebra.pointsEquiv_naturality`, `coefficientHom_naturality`,
  `UnitaryTwistedChart.Cocycle.suChart_naturality`, `SpecialLinear.pointsEquiv_naturality`
  and `E.naturality`.
- Matrix identities: `conj_conj_cancel` (`X (X⁻¹ g X) X⁻¹ = g`), `inv_transpose_conj`
  (if `h = (Y⁻¹ g⁻¹ Y)ᵀ` in `SL` then `(h⁻¹)ᵀ = Y⁻¹ g Y`), `inner_cancel` and
  `outer_cancel`.
- `localEquiv_coverAut`: assume the matrix discrepancy formulas of the published
  `OuterTypeAUnitarySplit.IsInnerMatrixFormula E σ (c.x σ)` for every `σ` fixing `F` and
  `OuterTypeAUnitarySplit.IsOuterMatrixFormula E σ (c.x σ)` for every other `σ`. Then
  `localEquiv c E (a ≫ coverAut K M σ) = localEquiv c E a`. Write `ψ = coefficientHom a`,
  `X` the image of `x σ` and `g` the chart of a point along `ψ`. If `σ` fixes `F`, the chart
  along `ψ ∘ σ` is `X⁻¹ g X` (`suChart_comp_of_mem`), and the inner discrepancy sends it to
  `g`. Otherwise it is `(X⁻¹ g⁻¹ X)ᵀ` (`suChart_comp_of_not_mem`), and the outer discrepancy
  `h ↦ X (h⁻¹)ᵀ X⁻¹` sends it to `g`. The published
  `OuterTypeAHermitian.toFun_coverAut_of_discrepancy` converts this into the claim.
- `localIso c E` (def) packages the local isomorphisms as a `LocalGroupIso`;
  `localIso_isInvariant` restates `localEquiv_coverAut` as `LocalGroupIso.IsInvariant`.
- `descendedIso c E hin hout : SU(B, τ) ≅ G` (def), for `G` with affine structure morphism,
  is the published `LocalGroupIso.galoisDescendIso` applied to `localIso c E`.

## The reduction

`isInnerMatrixFormula_of_hasInnerDiscrepancy` converts the published `HasInnerDiscrepancy` into
`IsInnerMatrixFormula` (the converse of the published `hasInnerDiscrepancy_of_matrix`).

`outerTypeAUnitaryAlgebraPresentation_of_specialLinearTitsCocycle` assumes
`SpecialLinearTitsCocycleStatement.{u}` and proves
`OuterTypeAUnitaryAlgebraPresentationStatement.{u}`. Given `K`, `G`, `d`, `n` and the
hypotheses:

1. As in the published `outerTypeAUnitarySplitPresentation_of_specialLinearTitsCocycle`, the
   nontrivial star action gives the star image pair (`starImagePair_of_A`), the Tits cocycle
   gives `M`, `E` and `x`, the star field embeds into `M` (`starFieldToCover`), and `F` is
   its image, a separable quadratic extension of `K` whose fixing subgroup has index two.
   The discrepancies are inner on that subgroup and outer off it, so `x` satisfies the twisted
   projective cocycle law (`isTwistedProjectiveCocycle_of_discrepancy`).
2. Some `r` lies outside the fixing subgroup, since its index is two. This gives
   `c = ⟨x, …, r, …⟩ : Cocycle F (Fin (n + 1))`.
3. The witnesses are `E := F`, `B := c.Alg` with its subalgebra structures and the
   instances of `UnitaryTwistedChart`, and `τ := c.involution`. The conjugation clause is
   `c.involution_algebraMap`, the dimension clause is `c.finrank_alg`
   (`(n + 1) * (n + 1) = (n + 1)^2`), and the presentation is
   `UnitaryAlgebra.Presentation.ofIso F τ (descendedIso c E hin hout)`.

No coordinate change of the cocycle and no splitting hypothesis on `K` is used.

## Provenance

Internal. This is the Galois-descent proof that an outer form of `SL_(n+1)` is the special
unitary group of a central simple algebra of degree `n + 1` with a unitary involution over the
quadratic star field, the essential surjectivity part of Knus, Merkurjev, Rost and Tignol,
*The Book of Involutions* (1998), Theorem (26.9), printed p. 366. The Lean route follows the
published reduction in `OuterTypeAUnitarySplitReduction` up to the twisted cocycle and then
descends the matrix algebra itself instead of splitting it.
