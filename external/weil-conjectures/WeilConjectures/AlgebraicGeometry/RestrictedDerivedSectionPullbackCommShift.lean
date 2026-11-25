/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RestrictedDerivedSectionsShiftTransport
import all WeilConjectures.AlgebraicGeometry.RestrictedDerivedSectionsShiftTransport

/-! # Shift compatibility of restricted derived section pullback -/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale.RawRestrictedComparison

/-- The derived section pullback before applying homology. -/
noncomputable def restrictedDerivedSectionPullback {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (U : S.Etale) :
    Evaluation.functor
      (upperStar AddCommGrpCat.{u + 1} (Limits.pullback.snd U.hom h))
      (Sheaf.Γ (Limits.pullback U.hom h).smallEtaleTopology AddCommGrpCat.{u + 1}) ⟶
    D+(upperStar AddCommGrpCat.{u + 1} a) ⋙
      Evaluation.functor
        (upperStar AddCommGrpCat.{u + 1} (Limits.pullback.snd U.hom h'))
        (Sheaf.Γ (Limits.pullback U.hom h').smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  Functor.whiskerLeft
      (DerivedCategory.Plus.ι ⋙
        D(upperStar AddCommGrpCat.{u + 1} (Limits.pullback.snd U.hom h)))
      (derivedSectionPullback (rawAffineRestrictedMap a h h' w U)) ≫
    Functor.whiskerRight
      (Functor.whiskerLeft DerivedCategory.Plus.ι
        (derivedRestrictionIso a h h' w U).hom)
      (rightDerivedGlobalSections AddCommGrpCat.{u + 1} (Limits.pullback U.hom h'))

/-- Restricted derived section pullback commutes with shifts. -/
theorem restrictedDerivedSectionPullback_commShift {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (U : S.Etale) :
    NatTrans.CommShift (restrictedDerivedSectionPullback a h h' w U) ℤ := by
  let A := (DerivedCategory.Plus.ι :
    DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤ _)
  let B := (DerivedCategory.Plus.ι :
    DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤ _)
  let R := D(upperStar AddCommGrpCat.{u + 1} (Limits.pullback.snd U.hom h))
  let R' := D(upperStar AddCommGrpCat.{u + 1} (Limits.pullback.snd U.hom h'))
  let N := D(upperStar AddCommGrpCat.{u + 1} a)
  let L := D+(upperStar AddCommGrpCat.{u + 1} a)
  let M := D(upperStar AddCommGrpCat.{u + 1} (rawAffineRestrictedMap a h h' w U))
  let P := rightDerivedGlobalSections AddCommGrpCat.{u + 1} (Limits.pullback U.hom h)
  let Q := rightDerivedGlobalSections AddCommGrpCat.{u + 1} (Limits.pullback U.hom h')
  let τ := restrictedDerivedSectionPullback a h h' w U
  have hcomp : NatTrans.CommShift
      (upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlusCompatibility.inv ℤ := by
    change NatTrans.CommShift
      (DerivedCategory.TStructure.t.plus.liftCompιIso
        (A ⋙ N) (fun X ↦ (L.obj X).2)).inv ℤ
    infer_instance
  have hrestriction := restriction_commShift a h h' w U
  have hpullback := pullback_commShift (rawAffineRestrictedMap a h h' w U)
  let β : R ⋙ P ⟶ N ⋙ R' ⋙ Q :=
    Functor.whiskerLeft R (derivedSectionPullback (rawAffineRestrictedMap a h h' w U)) ≫
      (Functor.associator R M Q).inv ≫
      Functor.whiskerRight (derivedRestrictionIso a h h' w U).hom Q ≫
      (Functor.associator N R' Q).hom
  have hβ : NatTrans.CommShift β ℤ := by
    dsimp only [β, R, R', N, M, P, Q]
    infer_instance
  have heq : τ =
      Functor.whiskerLeft A β ≫
        (Functor.associator A N (R' ⋙ Q)).inv ≫
        Functor.whiskerRight
          (upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlusCompatibility.inv
          (R' ⋙ Q) ≫
        (Functor.associator L B (R' ⋙ Q)).hom := by
    ext X
    simp only [Functor.comp_obj, Functor.id_obj, Functor.const_obj_obj, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.associator_inv_app, ObjectProperty.ι_obj,
      Functor.whiskerRight_app, Functor.comp_map, Functor.associator_hom_app,
      Category.id_comp]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id]
    dsimp only [τ, β, A, R, R', N, M, Q, P, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, NatTrans.comp_app, Functor.associator_hom_app,
      Functor.associator_inv_app, restrictedDerivedSectionPullback]
    simp only [Category.id_comp, Category.comp_id]
    exact (Category.comp_id _).symm
  exact lift_composite_commShift A B N L (R ⋙ P) (R' ⋙ Q) β
    (upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlusCompatibility τ heq

end AlgebraicGeometry.Etale.RawRestrictedComparison
