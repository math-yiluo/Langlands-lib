/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.CartesianChartClassPullback
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeCoefficients
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompAssoc
-- Internal comparison lemmas are shared through private imports.
set_option linter.privateModule false

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
set_option backward.isDefEq.respectTransparency true
set_option linter.unusedSimpArgs false
set_option linter.privateModule false

variable (A : Type (u + 2)) [Category.{u + 1} A]
  [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

private lemma single_source {S Y Z : Scheme.{u}} (a : Z ⟶ Y) (h : Y ⟶ S)
    (h' : Z ⟶ S) (w : h' = a ≫ h)
    (M : Sheaf S.smallEtaleTopology A) :
    (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp A a h h' w).hom.app M) ≫
      (((a)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ =
    (((h')^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app M ≫
      (upperStarCompDerivedPlus A a h h' w).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M) ≫
      D+((a)^*[A]).map
        ((((h)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app M) := by
  apply (cancel_epi
    ((((h')^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app M)).1
  simp only [Category.assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc, Category.comp_id]
  rw [← reassoc_of% (comp_single A a h h' w M)]
  simp only [Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc,
    Category.comp_id]

private lemma single_restriction {S Y Z : Scheme.{u}} (a : Z ⟶ Y) (h : Y ⟶ S)
    (h' : Z ⟶ S) (w : h' = a ≫ h)
    (M : Sheaf S.smallEtaleTopology A) :
    (((a)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp A a h h' w).inv.app M) =
    D+((a)^*[A]).map
        ((((h)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app M) ≫
      (upperStarCompDerivedPlus A a h h' w).inv.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M) ≫
      (((h')^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app M := by
  apply (cancel_mono
    ((((h')^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app M)).1
  simpa only [Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app, Category.comp_id] using
    comp_single_inv A a h h' w M

private lemma square_comp {B T T' Z Z' : Scheme.{u}}
    (t : Z' ⟶ Z) (p : Z ⟶ T) (p' : Z' ⟶ T') (b : T' ⟶ T)
    (sq : CommSq t p' p b) (a : T ⟶ B) (a' : T' ⟶ B) (ha : a' = b ≫ a)
    (s : Z ⟶ B) (hs : s = p ≫ a) (s' : Z' ⟶ B) (hs' : s' = p' ≫ a')
    (M : DerivedCategory.Plus (Sheaf B.smallEtaleTopology A)) :
    D+((p')^*[A]).map
        ((upperStarCompDerivedPlus A b a a' ha).hom.app M) ≫
      (pullbackSquareComparison A sq).hom.app
        (D+((a)^*[A]).obj M) ≫
      D+((t)^*[A]).map
        ((upperStarCompDerivedPlus A p a s hs).inv.app M) =
    (upperStarCompDerivedPlus A p' a' s' hs').inv.app M ≫
      (upperStarCompDerivedPlus A t s s'
        (by rw [hs', ha, ← Category.assoc p' b a, ← sq.w, Category.assoc, ← hs])).hom.app M := by
  let d := t ≫ p
  have hd : d = p' ≫ b := sq.w
  have hds : s' = d ≫ a := by rw [hs', ha, ← Category.assoc p' b a, ← hd]
  have h₁ := NatTrans.congr_app (upperStarCompDerivedPlus_assoc
    A t p a d s s' rfl hs hds) M
  have h₂ := NatTrans.congr_app (upperStarCompDerivedPlus_assoc
    A p' b a d a' s' hd ha hds) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h₁ h₂
  dsimp only [d] at h₁ h₂ hd hds
  rw [pullbackSquareComparison_eq]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  apply (cancel_epi
    ((upperStarCompDerivedPlus A p' a' s' hs').hom.app M)).1
  simp only [Category.assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc, Category.comp_id]
  rw [reassoc_of% h₂]
  simp only [Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc,
    Category.comp_id]
  rw [← reassoc_of% h₁]
  simp only [← Functor.map_comp, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]

end AlgebraicGeometry.Etale
