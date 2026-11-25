/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Ring evaluation of finite biproduct matrices -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.InternalPerfectMatrix

/-- A ring map from a commutative ring into endomorphisms carries products to composition. -/
theorem ringEntry_comp {C : Type*} [Category* C] [Preadditive C]
    {R : Type*} [CommRing R] (M : C) (e : R →+* End M) (a b : R) :
    (e a).asHom ≫ (e b).asHom = (e (a * b)).asHom := by
  rw [mul_comm a b, map_mul]
  rfl

/-- Entrywise ring evaluation respects finite matrix composition. -/
theorem ringMatrix_comp {C : Type*} [Category* C] [Preadditive C]
    [HasFiniteBiproducts C] {R : Type*} [CommRing R]
    (M : C) (e : R →+* End M) {I J K : Type} [Finite I] [Fintype J] [Finite K]
    (a : I → J → R) (b : J → K → R) :
    biproduct.matrix (fun i j ↦ (e (a i j)).asHom) ≫
      biproduct.matrix (fun j k ↦ (e (b j k)).asHom) =
        biproduct.matrix (fun i k ↦ (e (∑ j, a i j * b j k)).asHom) := by
  apply biproduct.hom_ext'
  intro i
  apply biproduct.hom_ext
  intro k
  simp only [Category.assoc, biproduct.ι_matrix_assoc, biproduct.matrix_π,
    biproduct.lift_desc, biproduct.ι_desc, map_sum]
  rw [End.sum_asHom]
  congr 1
  funext j
  exact ringEntry_comp M e _ _

/-- Entrywise ring evaluation respects addition of finite matrices. -/
theorem ringMatrix_add {C : Type*} [Category* C] [Preadditive C]
    [HasFiniteBiproducts C] {R : Type*} [CommRing R]
    (M : C) (e : R →+* End M) {I J : Type} [Finite I] [Finite J]
    (a b : I → J → R) :
    biproduct.matrix (fun i j ↦ (e (a i j + b i j)).asHom) =
      biproduct.matrix (fun i j ↦ (e (a i j)).asHom) +
        biproduct.matrix (fun i j ↦ (e (b i j)).asHom) := by
  ext i j
  simp [biproduct.matrix, map_add, Preadditive.comp_add, Preadditive.add_comp]

/-- Entrywise ring evaluation respects the integral unit sign of a Hom differential. -/
theorem ringMatrix_units_smul {C : Type*} [Category* C] [Preadditive C]
    [HasFiniteBiproducts C] {R : Type*} [CommRing R]
    (M : C) (e : R →+* End M) {I J : Type} [Finite I] [Finite J]
    (a : I → J → R) (s : ℤˣ) :
    biproduct.matrix (fun i j ↦ (e (s • a i j)).asHom) =
      s • biproduct.matrix (fun i j ↦ (e (a i j)).asHom) := by
  ext i j
  simp only [biproduct.matrix, Units.smul_def, map_zsmul, End.zsmul_asHom,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    biproduct.ι_desc_assoc, biproduct.lift_π]

end AlgebraicGeometry.ProEtale.InternalPerfectMatrix
