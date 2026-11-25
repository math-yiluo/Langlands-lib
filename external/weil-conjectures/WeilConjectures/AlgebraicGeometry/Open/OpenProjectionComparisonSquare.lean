/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonOpenTensorCoherence
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Site transport of the open projection formula

## References

* Stacks Project, Tag 09AF
* Tag 0GL1
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The comparison square for the canonical open projection maps, for arbitrary
unbounded derived objects. The two displayed composites use the fixed adjoint-normalized
extension comparison, the tensor comparison of exact comparison pullback, and the
exact-to-left-derived restriction comparisons. -/
theorem openProjectionTransport_projection_square
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (F : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (B : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map
        (((Etale.derivedOpenImmersionLowerShriekProjectionMap
          (ModuleCat.{u + 1} Λ) j).app F).app B) ≫
      ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} Λ)
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj F)).app B ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).mapIso
      (((Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) j) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm)).app F)).app _).hom =
    (((Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) j) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm)).app _ ≪≫
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.mapIso
      (((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} Λ) F).app _) ≪≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj _).mapIso
          (((Functor.isoWhiskerRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j) _ ≪≫
    (Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) j) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm).symm ≪≫
    Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).symm)).app B))).hom ≫
      ((derivedOpenImmersionLowerShriekProjectionMap (ModuleCat.{u + 1} Λ) j).app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory.obj F)).app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj B) := by
  have hsupport : supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) j =
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) j).symm := by
    have hd : supportSiteComparisonCoefficientDirectImageIso (ModuleCat.{u + 1} Λ) j =
        lowerStarCompComparisonLowerStarIso j (ModuleCat.{u + 1} Λ) := by
      apply Iso.ext
      apply NatTrans.ext
      funext G
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext W
      simp only [supportSiteComparisonCoefficientDirectImageIso,
        lowerStarCompComparisonLowerStarIso, Iso.trans_hom, Iso.symm_hom,
        NatTrans.comp_app, Functor.sheafPushforwardContinuousComp,
        Functor.sheafPushforwardContinuousIso,
        supportSiteComparisonSiteBaseChangeIso, toProEtCompOverPullbackIso,
        Iso.refl_hom, NatTrans.id_app]
      rfl
    change ((conjugateIsoEquiv _ _).symm
      (supportSiteComparisonCoefficientDirectImageIso (ModuleCat.{u + 1} Λ) j).symm).symm = _
    rw [hd]
    rfl
  let C := (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory
  let CU := (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory
  let e := ((Etale.derivedOpenImmersionLowerShriekProjectionIso
    (ModuleCat.{u + 1} Λ) j).app F).app B
  let p := ((derivedOpenImmersionLowerShriekProjectionIso
    (ModuleCat.{u + 1} Λ) j).app (CU.obj F)).app (C.obj B)
  let s := (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
    (ModuleCat.{u + 1} Λ) j).hom.app _ ≫
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.map
      (comparisonOpenTensorIso Λ j F B).hom
  let t := (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
    (ModuleCat.{u + 1} Λ)
    ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj F)).hom.app B ≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).map
      ((mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} Λ) j).hom.app F)).app (C.obj B)
  have h : C.map e.inv ≫ s = t ≫ p.inv := by
    simpa only [s, t, e, p, C, CU, Iso.app_inv, Category.assoc] using
      comparison_open_tensor_coherence Λ j F B
  have h' : C.map e.hom ≫ t = s ≫ p.hom := by
    apply (cancel_epi (C.map e.inv)).1
    simp only [← Category.assoc, ← C.map_comp, Iso.inv_hom_id, C.map_id,
      Category.id_comp]
    rw [h]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simpa [C, CU, e, p, s, t, comparisonOpenTensorIso, comparisonOpenDerivedPullbackIso,
    mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso,
    hsupport, Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc] using h'

end AlgebraicGeometry.ProEtale
