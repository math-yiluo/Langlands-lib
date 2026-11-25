/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap
public import WeilConjectures.AlgebraicGeometry.AbelianFreeRepresentablePullback

/-! # Pullback of derived Hom classes across a test-object square

Source: Stacks Project, Tags 03CB, 03Q8 and 0EYM.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The map on the free-sheaf sources of the derived Hom classes.
The test-object arrow first maps the free sheaf on `W'` to the pullback of
that on `W`. Pullback by `h'`, followed by inverse-image composition across
`sq`, produces a morphism to `a^* h^* ℤ[W]`.
Source: Stacks Project, Tags 03CB and 03Q8.
(blueprint: def-sf-higher-image-cohomology-square-raw-map). -/
noncomputable def higherImageCohomologySquareRawSource
    {Y Y' S S' : Scheme.{u}}
    {h : Y ⟶ S} {h' : Y' ⟶ S'} {a : Y' ⟶ Y} {b : S' ⟶ S}
    (sq : CommSq a h' h b) {W : S.Etale} {W' : S'.Etale}
    (v : W'.left ⟶ W.left) (hv : v ≫ W.hom = W'.hom ≫ b) :
    (upperStar AddCommGrpCat.{u + 1} h').obj ((abelianComparisonFree S').obj W') ⟶
      (upperStar AddCommGrpCat.{u + 1} a).obj
        ((upperStar AddCommGrpCat.{u + 1} h).obj ((abelianComparisonFree S).obj W)) := by
  let A := (abelianComparisonFree S).obj W
  let U := (MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) b).obj W
  let l : W' ⟶ U := MorphismProperty.Over.homMk
    (Limits.pullback.lift v W'.hom hv) (by simp [U])
  let ψ := (abelianComparisonFree S').map l ≫
    (abelianFreeRepresentablePullbackIso b W).inv
  exact (upperStar AddCommGrpCat.{u + 1} h').map ψ ≫
    (upperStarComp AddCommGrpCat.{u + 1} h' b (h' ≫ b) rfl).inv.app A ≫
    (eqToIso (congrArg (fun k : Y' ⟶ S =>
      (upperStar AddCommGrpCat.{u + 1} k).obj A) sq.w.symm)).hom ≫
    (upperStarComp AddCommGrpCat.{u + 1} a h (a ≫ h) rfl).hom.app A

/-- The explicit raw square pullback. It uses only the free-sheaf source map,
the exact inverse-image single and shift comparisons, and the coefficient map.
No cohomology comparison or higher-direct-image exchange is used to define it.
Source: Stacks Project, Tags 03Q8, 07A7 and 0EYM.
(blueprint: def-sf-higher-image-cohomology-square-raw-map). -/
noncomputable def higherImageCohomologySquareRawMap
    {Y Y' S S' : Scheme.{u}}
    {h : Y ⟶ S} {h' : Y' ⟶ S'} {a : Y' ⟶ Y} {b : S' ⟶ S}
    (sq : CommSq a h' h b)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} a).obj F ⟶ F')
    (p : ℕ) {W : S.Etale} {W' : S'.Etale}
    (v : W'.left ⟶ W.left) (hv : v ≫ W.hom = W'.hom ≫ b)
    (z : (abelianHigherDirectImageRawPresheaf h p F).obj (op W)) :
    (abelianHigherDirectImageRawPresheaf h' p F').obj (op W') :=
  (DerivedCategory.Plus.singleFunctor _ 0).map
      (higherImageCohomologySquareRawSource sq v hv) ≫
    ((upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
    (upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlus.map z ≫
    ((upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlus.commShiftIso
      (p : ℤ)).hom.app ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
    (shiftFunctor _ (p : ℤ)).map
      (((upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map φ)

end AlgebraicGeometry.Etale
