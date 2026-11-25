/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.StrictTowerArithmetic.StrictTowerArithmeticRestrictionDefs
import WeilConjectures.CategoryTheory.StrictTowerArithmetic.StrictTowerArithmeticRestrictionResolution
import Mathlib.CategoryTheory.Limits.Final
/-! # The normalized derived arithmetic comparison

Source: Stacks Project, Tags 0941 and 0H9K; uniqueness of right derived functors.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
universe a b w uC vC r
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.StrictTowerArithmetic
private def ceilIndex (e : ℕ) : ℕᵒᵖ ⥤ ℕᵒᵖ :=
  (show ℕ →o ℕ from
    { toFun := fun n ↦ n / e
      monotone' := fun _ _ h ↦ Nat.div_le_div_right h }).monotone.functor.op
private lemma arithmetic_gc (e : ℕ) (he : 1 ≤ e) (i n : ℕ) :
    i / e ≤ n ↔ i ≤ e * (n + 1) - 1 := by
  have hp : 0 < e := he
  rw [Nat.div_le_iff_le_mul_add_pred hp]
  rw [Nat.mul_add, Nat.mul_one]
  omega
private def indexAdjunction (e : ℕ) (he : 1 ≤ e) : index e ⊣ ceilIndex e :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun n i ↦
        { toFun := fun f ↦ (homOfLE ((arithmetic_gc e he i.unop n.unop).2 f.unop.le)).op
          invFun := fun f ↦ (homOfLE ((arithmetic_gc e he i.unop n.unop).1 f.unop.le)).op
          left_inv := fun _ ↦ Subsingleton.elim _ _
          right_inv := fun _ ↦ Subsingleton.elim _ _ } }
private lemma limitMap_isIso
    (A : Type a) [Category.{b} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    (e : ℕ) (he : 1 ≤ e) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    IsIso (limitMap e I) := by
  have : (index e).Initial := Functor.initial_of_adjunction (indexAdjunction e he)
  have (i : ℤ) : IsIso ((limitMap e I).f i) := by
    dsimp [limitMap]
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

variable (A : Type a) [Category.{b} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
  (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
  (η : limitComplex A ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
private noncomputable def limitNat (e : ℕ) :
    limitComplex A ⟶ complexRestriction A e ⋙ limitComplex A where
  app X := limitMap e X
  naturality X Y f := by
    ext i
    exact limit.map_pre (f.f i) (index e)
private noncomputable def comparisonUnit (e : ℕ) :
    limitComplex A ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (derivedRestriction A e ⋙ RF) :=
  Functor.whiskerRight (limitNat A e) DerivedCategory.Q ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (complexRestriction A e) η ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (restriction A e).mapDerivedCategoryFactors.inv RF ≫
    (Functor.associator _ _ _).hom
private lemma comparisonUnit_app (e : ℕ) (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (comparisonUnit A RF η e).app X =
      DerivedCategory.Q.map (limitMap e X) ≫
        η.app ((complexRestriction A e).obj X) ≫
        RF.map ((restriction A e).mapDerivedCategoryFactors.inv.app X) := by
  simp [comparisonUnit, limitNat]

private noncomputable def comparison (e : ℕ)
    (hRF : RF.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))) :
    RF ⟶ derivedRestriction A e ⋙ RF := by
  let _ := hRF
  exact RF.rightDerivedDesc η
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) _ (comparisonUnit A RF η e)
private lemma comparison_fac (e : ℕ)
    (hRF : RF.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)))
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    η.app X ≫ (comparison A RF η e hRF).app (DerivedCategory.Q.obj X) ≫
        RF.map ((restriction A e).mapDerivedCategoryFactors.hom.app X) =
      DerivedCategory.Q.map (limitMap e X) ≫ η.app ((complexRestriction A e).obj X) := by
  let _ := hRF
  have h := RF.rightDerived_fac_app η
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) _ (comparisonUnit A RF η e) X
  change η.app X ≫ (comparison A RF η e hRF).app _ = _ at h
  rw [← Category.assoc, h, comparisonUnit_app]
  simp
private lemma comparison_isIso (e : ℕ) (he : 1 ≤ e)
    (hRF : RF.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)))
    (hη : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I))
    (hres : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      ∃ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (j : X ⟶ I),
        I.IsKInjective ∧ QuasiIso j) :
    IsIso (comparison A RF η e hRF) := by
  have hI (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (hi : I.IsKInjective) :
      IsIso ((comparison A RF η e hRF).app (DerivedCategory.Q.obj I)) := by
    let _ := hi
    have := restriction_preservesKInjectives A e he I
    have := hη I hi
    have := hη _ (restriction_preservesKInjectives A e he I)
    have := limitMap_isIso A e he I
    have h := comparison_fac A RF η e hRF I
    have : IsIso (η.app I ≫ (comparison A RF η e hRF).app (DerivedCategory.Q.obj I) ≫
        RF.map ((restriction A e).mapDerivedCategoryFactors.hom.app I)) := by
      rw [h]
      infer_instance
    exact (isIso_comp_left_iff (η.app I) _).1
      (by simpa only [Category.assoc] using
        ((isIso_comp_right_iff _ (RF.map
          ((restriction A e).mapDerivedCategoryFactors.hom.app I))).1
            (by simpa only [Category.assoc] using this)))
  rw [NatTrans.isIso_iff_isIso_app]
  intro Z
  let Q := DerivedCategory.Q (C := ℕᵒᵖ ⥤ A)
  let X := Q.objPreimage Z
  obtain ⟨I,j,hi,hj⟩ := hres X
  let _ := hj
  let f := comparison A RF η e hRF
  have := hI I hi
  have := f.naturality (Q.map j)
  have : IsIso (f.app (Q.obj X)) := by
    have : IsIso (RF.map (Q.map j) ≫ f.app (Q.obj I)) := by infer_instance
    rw [f.naturality (Q.map j)] at this
    exact (isIso_comp_right_iff _ ((derivedRestriction A e ⋙ RF).map (Q.map j))).1 this
  exact (NatTrans.isIso_app_iff_of_iso f (Q.objObjPreimageIso Z)).1 this

end CategoryTheory.StrictTowerArithmetic
