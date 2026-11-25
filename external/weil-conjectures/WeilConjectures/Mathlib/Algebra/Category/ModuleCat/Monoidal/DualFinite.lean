/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Dualizable modules are finitely generated

If a module `M` over a commutative ring `R` has a right dual `N` in `ModuleCat R`, then `M` is
finitely generated: writing the coevaluation `1 ↦ ∑ mᵢ ⊗ nᵢ`, the zigzag identity gives
`m = ∑ ε(nᵢ ⊗ m) • mᵢ` for every `m : M`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory TensorProduct

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- A module with a right dual in `ModuleCat R` is finitely generated. -/
theorem finite_of_exactPairing (M N : ModuleCat.{u} R) [ExactPairing M N] :
    Module.Finite R M := by
  obtain ⟨J, hJ, y, hy⟩ := Submodule.exists_fg_le_eq_rTensor_subtype (R := R)
    ((η_ M N).hom (1 : R))
  rw [Module.finite_def, ← (show J = ⊤ from ?_)]
  · exact hJ
  rw [eq_top_iff]
  intro m _
  -- the composite `M ⊗ N ⟶ M`, `x ⊗ n ↦ ε(n ⊗ m) • x`
  let ψ : N →ₗ[R] R := (ε_ M N).hom ∘ₗ (TensorProduct.mk R N M).flip m
  let φ : (M : Type u) ⊗[R] N →ₗ[R] M := TensorProduct.rid R M ∘ₗ LinearMap.lTensor M ψ
  have h₁ : ∀ z : (M : Type u) ⊗[R] N,
      ((M ◁ ε_ M N) ((α_ M N M).hom (z ⊗ₜ m)) : (M : Type u) ⊗[R] R) =
        LinearMap.lTensor M ψ z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x n => rfl
    | add x z hx hz => simp only [TensorProduct.add_tmul, map_add, hx, hz]
  have h₂ := congr(($(ExactPairing.evaluation_coevaluation M N)).hom ((1 : R) ⊗ₜ[R] m))
  simp only [hom_comp, LinearMap.comp_apply, MonoidalCategory.leftUnitor_hom_apply, one_smul,
    MonoidalCategory.rightUnitor_inv_apply] at h₂
  have h₃ : φ ((η_ M N).hom (1 : R)) = m := by
    simp only [φ, LinearMap.comp_apply]
    erw [← h₁, h₂]
    simp
  rw [← h₃, hy]
  clear hy h₃ h₂
  induction y using TensorProduct.inductionOn with
  | tmul x n =>
    simp only [φ, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
    exact J.smul_mem _ x.2
  | add x z hx hz => rw [map_add, map_add]; exact J.add_mem hx hz

end ModuleCat
