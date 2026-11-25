/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap
import WeilConjectures.AlgebraicGeometry.RestrictedComparisonGeneratorPullback

/-! # Pullback compatibility of restricted derived-Hom evaluation

Source: Stacks Project, Tags 03Q8, 0D6F and 07A6.
(blueprint: lem-sbc-raw-restricted-cohomology-comparison-naturality).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- The explicit evaluation map commutes with the explicit raw pullback.
This asserts compatibility of a constructed map, independently of invertibility.
Source: Stacks Project, Tag 03Q8 and Cohomology on Sites, Tags 0D6F and 07A6.
(blueprint: lem-sbc-raw-restricted-cohomology-comparison-naturality).

Proof: Write V = U times_S Y, V' = U times_S Y', r : V -> Y,
r' : V' -> Y' and q : V' -> V. The pullback projection identities give
r' followed by a = q followed by r. Naturality of the sheafification unit and
of the inverse-image adjunction unit identifies the pullback of the represented
identity section on V with the represented identity section on V'. The
inverse-image composition isomorphisms transport the coefficient restriction
along this equality by exactly rawAffineRestrictedCoefficient. Apply restricted
derived sections to the five factors defining abelianHigherDirectImageRawPullback.
Naturality of mapDerivedCategorySingleFunctor and mapDerivedCategoryFactors
moves the single-complex comparisons to the ends. Naturality of the derived
inverse-image/direct-image adjunction unit, with the triangle identities,
identifies the intervening map on derived sections with the unit followed by
the derived global-sections composition comparison; this is the derived map
whose homology defines rawAffineComplexPullback. The shift comparisons commute
with these maps, so zeroth homology on the shifted object becomes p-th homology
on the unshifted restricted single complex. Evaluate the resulting commuting
square at the represented identity generator. The left composite is the
restricted cohomology map after evaluation, and the right composite is evaluation
after the raw pullback. These are the two sides of the stated equality.
This calculation involves no inverse to the evaluation map and works also in
degree zero and when either restricted scheme is empty. -/
theorem rawRestrictedCohomologyComparison_naturality {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : (upperStar AddCommGrpCat.{v + 1} a).obj F ⟶ F') (U : S.Etale)
    (t : (abelianHigherDirectImageRawPresheaf h p F).obj (op U)) :
    rawAffineRestrictedCohomologyMap a h h' w p F F' φ U
        (rawRestrictedCohomologyComparison h p F U t) =
      rawRestrictedCohomologyComparison h' p F' U
        (abelianHigherDirectImageRawPullback a h h' w p F F' φ U t) := by
  let G := (upperStar AddCommGrpCat.{v + 1} h).obj
    (RawRestrictedComparison.freeSheaf S U)
  let G' := (upperStar AddCommGrpCat.{v + 1} h').obj
    (RawRestrictedComparison.freeSheaf S U)
  let e : (upperStar AddCommGrpCat.{v + 1} a).obj G ≅ G' :=
    ((upperStarComp AddCommGrpCat.{v + 1} a h h' w.symm).app
      (RawRestrictedComparison.freeSheaf S U)).symm
  let x := (RawRestrictedComparison.zeroIso
    ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U) G).inv
      (RawRestrictedComparison.generator h U)
  have square := RawRestrictedComparison.restrictedDerivedEvaluation_pullback
    a h h' w p G G' e F F' φ U t
  have at_x := congrArg (fun f ↦ f x) square
  simp only [AddCommGrpCat.comp_apply] at at_x
  have gen := RawRestrictedComparison.restrictedComparison_generator_pullback a h h' w U
  change RawRestrictedComparison.transportZero a h h' w G G' e.hom U x = _ at gen
  rw [gen] at at_x
  change rawAffineRestrictedCohomologyMap a h h' w p F F' φ U
      ((RawRestrictedComparison.shiftIso h p F U).hom
        ((RawRestrictedComparison.Hzero h U).map t x)) = _
  exact at_x

end AlgebraicGeometry.Etale
