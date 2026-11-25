/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Quasi-inverses of morphisms with torsion kernel and cokernel

In an abelian category, a morphism `φ : M ⟶ N` whose kernel is killed by `a : ℤ` and whose
cokernel is killed by `b : ℤ` has a quasi-inverse up to `a * b`: a morphism `ψ : N ⟶ M` with
`φ ≫ ψ = (a * b) • 𝟙 M` and `ψ ≫ φ = (a * b) • 𝟙 N`
(`CategoryTheory.Abelian.exists_comp_eq_zsmul_id_of_zsmul_kernel_ι_eq_zero`).
-/

@[expose] public section

namespace CategoryTheory.Abelian

open Limits

variable {C : Type*} [Category C] [Abelian C]

/-- **Morphisms with torsion kernel and cokernel are invertible up to a scalar**: if the kernel of
`φ : M ⟶ N` is killed by `a` and its cokernel by `b`, then there is `ψ : N ⟶ M` with
`φ ≫ ψ = (a * b) • 𝟙 M` and `ψ ≫ φ = (a * b) • 𝟙 N`. It is the composite of the lift
`N ⟶ im φ` of `b • 𝟙 N` and the descent `im φ ⟶ M` of `a • 𝟙 M`. -/
theorem exists_comp_eq_zsmul_id_of_zsmul_kernel_ι_eq_zero {M N : C} (φ : M ⟶ N) {a b : ℤ}
    (ha : a • kernel.ι φ = 0) (hb : b • cokernel.π φ = 0) :
    ∃ ψ : N ⟶ M, φ ≫ ψ = (a * b) • 𝟙 M ∧ ψ ≫ φ = (a * b) • 𝟙 N := by
  have hp : kernel.ι (Limits.factorThruImage φ) ≫ (a • 𝟙 M) = 0 := by
    have h : kernel.ι (Limits.factorThruImage φ) ≫ φ = 0 := by
      calc kernel.ι (Limits.factorThruImage φ) ≫ φ =
          (kernel.ι (Limits.factorThruImage φ) ≫ Limits.factorThruImage φ) ≫
            Limits.image.ι φ := by rw [Category.assoc, Limits.image.fac]
        _ = 0 := by rw [kernel.condition, zero_comp]
    rw [Preadditive.comp_zsmul, Category.comp_id, ← kernel.lift_ι φ _ h, ← Preadditive.comp_zsmul,
      ha, comp_zero]
  have hi : (b • 𝟙 N) ≫ cokernel.π (Limits.image.ι φ) = 0 := by
    have h : φ ≫ cokernel.π (Limits.image.ι φ) = 0 := by
      rw [← Limits.image.fac_assoc, cokernel.condition, comp_zero]
    rw [Preadditive.zsmul_comp, Category.id_comp, ← cokernel.π_desc φ _ h,
      ← Preadditive.zsmul_comp, hb, zero_comp]
  let h := epiDesc (Limits.factorThruImage φ) _ hp
  let g := monoLift (Limits.image.ι φ) _ hi
  have hh : h ≫ Limits.factorThruImage φ = a • 𝟙 _ := by
    rw [← cancel_epi (Limits.factorThruImage φ), ← Category.assoc, comp_epiDesc,
      Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.id_comp, Category.comp_id]
  have hg : Limits.image.ι φ ≫ g = b • 𝟙 _ := by
    rw [← cancel_mono (Limits.image.ι φ), Category.assoc, monoLift_comp,
      Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.id_comp, Category.comp_id]
  refine ⟨g ≫ h, ?_, ?_⟩
  · rw [← Limits.image.fac_assoc φ (g ≫ h), ← Category.assoc (Limits.image.ι φ), hg,
      Preadditive.zsmul_comp, Category.id_comp, Preadditive.comp_zsmul, comp_epiDesc,
      smul_smul, mul_comm]
  · have hφ : h ≫ φ = (h ≫ Limits.factorThruImage φ) ≫ Limits.image.ι φ := by
      rw [Category.assoc, Limits.image.fac]
    rw [Category.assoc, hφ, hh, Preadditive.zsmul_comp, Category.id_comp, Preadditive.comp_zsmul,
      monoLift_comp, smul_smul]

end CategoryTheory.Abelian
