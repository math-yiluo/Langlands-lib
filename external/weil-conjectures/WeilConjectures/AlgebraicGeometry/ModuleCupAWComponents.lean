/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementCosimplicialInput
public import Mathlib.Algebra.Homology.Monoidal

/-! # Explicit Alexander--Whitney components

Source: Banerjee, Tensor Structure on Smooth Motives, §1.1.4, p. 16.
(blueprint: def-sc-module-cup-aw-components).
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicTopology Simplicial

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The front/back formula on one summand, zero if either degree is negative.
Source: Banerjee, §1.1.4, p. 16 (blueprint: def-sc-module-cup-aw-components). -/
def moduleCup_awSummand (X : Scheme.{u}) [MonoidalPreadditive X.Modules]
    (A B C : CosimplicialObject X.Modules) (μ : moduleCup_cosimplicialTensor X A B ⟶ C)
    (r s n : ℤ) (h : r + s = n) :
    (moduleCup_cosimplicialComplex X A).X r ⊗
      (moduleCup_cosimplicialComplex X B).X s ⟶ (moduleCup_cosimplicialComplex X C).X n :=
  if hr : 0 ≤ r then
    if hs : 0 ≤ s then
      ((((alternatingCofaceMapComplex X.Modules).obj A).extendXIso
          ComplexShape.embeddingUpNat (i := r.toNat) (by simpa using Int.toNat_of_nonneg hr)).hom
        ⊗ₘ (((alternatingCofaceMapComplex X.Modules).obj B).extendXIso
          ComplexShape.embeddingUpNat (i := s.toNat) (by simpa using Int.toNat_of_nonneg hs)).hom)
      ≫ (A.map (SimplexCategory.subinterval 0 r.toNat (by omega)) ⊗ₘ
          B.map (SimplexCategory.subinterval r.toNat s.toNat (by omega)))
      ≫ μ.app ⦋r.toNat + s.toNat⦌
      ≫ (((alternatingCofaceMapComplex X.Modules).obj C).extendXIso
          ComplexShape.embeddingUpNat (i := r.toNat + s.toNat) (by
            change ((r.toNat + s.toNat : ℕ) : ℤ) = n
            rw [Nat.cast_add, Int.toNat_of_nonneg hr, Int.toNat_of_nonneg hs, h])).inv
    else 0
  else 0

/-- Assemble the summands by the coproduct universal property in each total degree.
Source: Banerjee, §1.1.4, p. 16 (blueprint: def-sc-module-cup-aw-components). -/
def moduleCup_awComponent (X : Scheme.{u}) [MonoidalPreadditive X.Modules]
    (A B C : CosimplicialObject X.Modules) (μ : moduleCup_cosimplicialTensor X A B ⟶ C)
    (n : ℤ) :
    (HomologicalComplex.tensorObj (moduleCup_cosimplicialComplex X A)
      (moduleCup_cosimplicialComplex X B)).X n ⟶ (moduleCup_cosimplicialComplex X C).X n :=
  HomologicalComplex.mapBifunctorDesc (fun r s h ↦ moduleCup_awSummand X A B C μ r s n h)

/-- Descent recovers the specified summand.
Source: coproduct universal property (blueprint: def-sc-module-cup-aw-components). -/
@[reassoc]
theorem moduleCup_ι_awComponent (X : Scheme.{u}) [MonoidalPreadditive X.Modules]
    (A B C : CosimplicialObject X.Modules) (μ : moduleCup_cosimplicialTensor X A B ⟶ C)
    (r s n : ℤ) (h : r + s = n) :
    HomologicalComplex.ιTensorObj (moduleCup_cosimplicialComplex X A)
      (moduleCup_cosimplicialComplex X B) r s n h ≫ moduleCup_awComponent X A B C μ n =
      moduleCup_awSummand X A B C μ r s n h := by
  apply HomologicalComplex.ι_mapBifunctorDesc

private theorem subinterval_zero_zero :
    SimplexCategory.subinterval (n := 0) 0 0 (by omega) = 𝟙 ⦋0⦌ := by
  apply SimplexCategory.Hom.ext_zero_left
  rfl

/-- Both front/back maps in bidegree zero are identities.
Source: Banerjee, §1.1.4, p. 16 (blueprint: def-sc-module-cup-aw-components). -/
theorem moduleCup_awSummand_zero (X : Scheme.{u}) [MonoidalPreadditive X.Modules]
    (A B C : CosimplicialObject X.Modules) (μ : moduleCup_cosimplicialTensor X A B ⟶ C) :
    moduleCup_awSummand X A B C μ 0 0 0 (by simp) =
      moduleCup_cosimplicialZeroPair X A B C μ := by
  simp only [moduleCup_awSummand, Std.le_refl, ↓reduceDIte, Int.toNat_zero,
    Nat.add_zero, subinterval_zero_zero, CategoryTheory.Functor.map_id,
    tensorHom_comp_tensorHom_assoc, moduleCup_cosimplicialZeroPair,
    moduleCup_cosimplicialZeroIso, Iso.cancel_iso_inv_right_assoc]
  erw [Category.comp_id, Category.comp_id]

end
end AlgebraicGeometry.Scheme.Modules
