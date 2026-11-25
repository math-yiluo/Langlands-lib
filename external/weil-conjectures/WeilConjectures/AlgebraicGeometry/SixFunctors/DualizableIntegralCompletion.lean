/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic

import WeilConjectures.AlgebraicGeometry.AdicCompletion.TensorIntegralReductionTower
import WeilConjectures.SixFunctors.ProEtale.InternalRoosOutputComplete
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.DerivedCategory.Products
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Dualizable tensoring preserves integral derived completeness

The statement concerns the actual augmented completion used by the coefficient library.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint

private def coneOfTriangle {A : Type*} [Category A]
    [HasZeroObject A] [HasShift A ℤ] [Preadditive A]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    (F : ℕᵒᵖ ⥤ A) [HasProduct (fun n : ℕ ↦ F.obj (Opposite.op n))]
    (L : A) (p : L ⟶ ∏ᶜ fun n : ℕ ↦ F.obj (Opposite.op n))
    (δ : (∏ᶜ fun n : ℕ ↦ F.obj (Opposite.op n)) ⟶ L⟦(1 : ℤ)⟧)
    (hT : IsDerivedLimitTriangle
      (fun n ↦ F.map (homOfLE n.le_succ).op) L p δ) : Cone F where
  pt := L
  π := NatTrans.ofOpSequence (fun n ↦ p ≫ Pi.π _ n) (by
    intro n
    simp only [Functor.const_obj_map]
    have hzero := Pretriangulated.comp_distTriang_mor_zero₁₂ _ hT
    have hn := congrArg (fun f ↦ f ≫ Pi.π (fun n : ℕ ↦ F.obj (Opposite.op n)) n) hzero
    simp only [zero_comp] at hn
    change (p ≫ towerTransitionEndomorphism
      (fun n ↦ F.map (homOfLE n.le_succ).op)) ≫ Pi.π _ n = 0 at hn
    simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.sub_comp,
      Category.id_comp, Pi.lift_comp_π, Preadditive.comp_sub, Category.assoc] at hn
    erw [Category.id_comp]
    simpa only [Category.assoc] using (sub_eq_zero.mp hn))

private theorem coneOfTriangle_milnor {A : Type*} [Category A]
    [HasZeroObject A] [HasShift A ℤ] [Preadditive A]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    (F : ℕᵒᵖ ⥤ A) [HasProduct (fun n : ℕ ↦ F.obj (Opposite.op n))]
    (L : A) (p : L ⟶ ∏ᶜ fun n : ℕ ↦ F.obj (Opposite.op n))
    (δ : (∏ᶜ fun n : ℕ ↦ F.obj (Opposite.op n)) ⟶ L⟦(1 : ℤ)⟧)
    (hT : IsDerivedLimitTriangle
      (fun n ↦ F.map (homOfLE n.le_succ).op) L p δ) :
    Pretriangulated.IsHomotopyLimit (coneOfTriangle F L p δ hT) := by
  let P : Fan (fun n : ℕ ↦ F.obj (Opposite.op n)) := Fan.mk _ (Pi.π _)
  let hP : IsLimit P := productIsProduct _
  refine ⟨P, hP, δ, ?_⟩
  have hp : Fan.IsLimit.lift hP
      (fun n ↦ (coneOfTriangle F L p δ hT).π.app (Opposite.op n)) = p := by
    apply Pi.hom_ext
    intro n
    exact Fan.IsLimit.fac hP _ n
  have ht : Pretriangulated.towerShift (F := F) hP =
      towerProductShift (fun n ↦ F.map (homOfLE n.le_succ).op) := by
    apply Pi.hom_ext
    intro n
    change Pretriangulated.towerShift hP ≫ P.proj n = _
    rw [Pretriangulated.towerShift, Fan.IsLimit.fac]
    simp only [towerProductShift, Pi.lift_comp_π]
    rfl
  rw [hp, ht]
  exact hT

/-- A dualizable object preserves the recorded continuous-coefficient derived completeness. -/
theorem dualizableIntegralCompletion
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (S : Scheme.{u}) (M : DerivedCategory (AdicCompletion.Modules l E S))
    (hM : IsDualizable M) :
    ∀ N : DerivedCategory (AdicCompletion.Modules l E S),
      IsDerivedComplete l E S N → IsDerivedComplete l E S (M ⊗ N) := by
  classical
  intro N hN
  obtain ⟨P, hP, ⟨eP⟩, hη⟩ := hN
  have : IsIso (DerivedCategory.Q.map (AdicCompletion.augmentation l E S P)) := hη
  let eN : N ≅ DerivedCategory.Q.obj (AdicCompletion.roos l E S P) :=
    eP.symm ≪≫ asIso (DerivedCategory.Q.map (AdicCompletion.augmentation l E S P))
  obtain ⟨_, δ, hT, _⟩ := AdicCompletion.roos_isDerivedLimit l E S N P hP eP
  let cN := coneOfTriangle (AdicCompletion.derivedTower l E S N) _ _ δ (by
    simpa only [AdicCompletion.derivedTower, Functor.ofOpSequence_map_homOfLE_succ] using hT)
  have hcN : Pretriangulated.IsHomotopyLimit cN := coneOfTriangle_milnor _ _ _ _ _
  obtain ⟨hdual⟩ := hM
  let : HasRightDual M := hdual
  let adj := tensorLeftAdjunction M Mᘁ
  have : (tensorLeft M).IsRightAdjoint := ⟨_, ⟨adj⟩⟩
  have : PreservesLimitsOfShape (Discrete ℕ) (tensorLeft M) := inferInstance
  have hmap := hcN.map (tensorLeft M)
  obtain ⟨a⟩ := AdicCompletion.tensorIntegralReductionTower l E S M N
  let c := (Cone.postcompose a.hom).obj ((tensorLeft M).mapCone cN)
  have hc : Pretriangulated.IsHomotopyLimit c :=
    hmap.of_iso a c (Iso.refl _) (by intro n; simp only [Iso.refl_hom, Category.id_comp]; rfl)
  obtain ⟨R, f, hf, _, hR⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (DerivedCategory.Q.objPreimage (M ⊗ N))
  have : QuasiIso f := hf
  let eR := asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso (M ⊗ N)
  obtain ⟨_, δR, hTR, _⟩ := AdicCompletion.roos_isDerivedLimit l E S (M ⊗ N) R hR eR
  let cR := coneOfTriangle (AdicCompletion.derivedTower l E S (M ⊗ N)) _ _ δR (by
    simpa only [AdicCompletion.derivedTower, Functor.ofOpSequence_map_homOfLE_succ] using hTR)
  have hcR : Pretriangulated.IsHomotopyLimit cR := coneOfTriangle_milnor _ _ _ _ _
  obtain ⟨e, _⟩ := hc.exists_iso hcR
  obtain ⟨Q, hQ, ⟨eQ⟩, hQη⟩ := AdicCompletion.isDerivedComplete_roos l E S R hR
  exact ⟨Q, hQ, ⟨eQ ≪≫ e.symm ≪≫ ((tensorLeft M).mapIso eN).symm⟩, hQη⟩

end AlgebraicGeometry.ProEtale
