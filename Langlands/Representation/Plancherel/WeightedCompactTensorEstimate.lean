import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.Complex.Basic

/-! # The norm estimate for a weighted tensor of ordered intertwiners -/

noncomputable section

open scoped TensorProduct

namespace Langlands.Plancherel

section Estimate

variable {V₀ V₁ V₂ D₀ D₁ : Type*}
  [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup D₀] [Module ℂ D₀]
  [AddCommGroup D₁] [Module ℂ D₁]
  {E₀ E₁ E₂ H₀ H₁ : Type*}
  [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀]
  [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℂ E₂]
  [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  (m₀ : V₀ ≃ₗ[ℂ] E₀) (m₁ : V₁ ≃ₗ[ℂ] E₁) (m₂ : V₂ ≃ₗ[ℂ] E₂)
  (d₀ : D₀ ≃ₗ[ℂ] H₀) (d₁ : D₁ ≃ₗ[ℂ] H₁)

/-- The estimate for one pure tensor. The first map of the normalized
comparison goes from `V₁` to `V₀`. The outer intertwiners go between `V₁`
and `V₂`. The Haar composition constant is retained in the bound. -/
theorem weightedTensor_norm_tmul_le
    (F : V₁ ≃ₗ[ℂ] V₀) (Q : D₀ →ₗ[ℂ] D₁)
    (T : V₀ →ₗ[ℂ] V₂) (S : V₁ →ₗ[ℂ] V₂) (R : V₂ →ₗ[ℂ] V₁)
    (c j w k : ℂ) (B : ℝ)
    (hcomp : T.comp F.toLinearMap = c • S)
    (hRT : R.comp S = j • LinearMap.id) (hw : w * j = k)
    (hR : ∀ v, ‖m₂ v‖ ≤ B * ‖m₁ (R v)‖)
    (hunit : ∀ v ℓ, ‖m₁ (F.symm v)‖ * ‖d₁ (Q ℓ)‖ = ‖m₀ v‖ * ‖d₀ ℓ‖)
    (v : V₀) (ℓ : D₀) :
    ‖TensorProduct.congr m₂ d₁ ((w • TensorProduct.map T Q) (v ⊗ₜ[ℂ] ℓ))‖ ≤
      (B * ‖c * k‖) * (‖m₀ v‖ * ‖d₀ ℓ‖) := by
  let v₁ := F.symm v
  have hv : F v₁ = v := F.apply_symm_apply v
  have hT : T v = c • S v₁ := by
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hv,
      LinearMap.smul_apply] using LinearMap.congr_fun hcomp v₁
  have hr : R (S v₁) = j • v₁ := LinearMap.congr_fun hRT v₁
  have hvalue : R (w • T v) = (c * k) • v₁ := by
    rw [hT, map_smul, map_smul, hr, smul_smul, smul_smul, mul_assoc, mul_left_comm w c, hw]
  have hn : ‖m₂ (w • T v)‖ ≤ (B * ‖c * k‖) * ‖m₁ v₁‖ := by
    calc
      _ ≤ B * ‖m₁ (R (w • T v))‖ := hR _
      _ = _ := by rw [hvalue, map_smul, norm_smul, mul_assoc]
  calc
    _ = ‖m₂ (w • T v)‖ * ‖d₁ (Q ℓ)‖ := by
      rw [LinearMap.smul_apply, TensorProduct.map_tmul, TensorProduct.smul_tmul',
        TensorProduct.congr_tmul, TensorProduct.norm_tmul]
    _ ≤ ((B * ‖c * k‖) * ‖m₁ v₁‖) * ‖d₁ (Q ℓ)‖ :=
      mul_le_mul_of_nonneg_right hn (norm_nonneg _)
    _ = _ := by rw [mul_assoc, hunit v ℓ]

end Estimate

section Additivity

variable {Z V D W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup D] [Module ℂ D] [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Pointwise boundedness of the operator family on pure tensors extends to
any fixed vector in the algebraic tensor product. -/
theorem exists_uniform_tensor_bound_of_tmul (J : Z → (V ⊗[ℂ] D) →ₗ[ℂ] W)
    (h : ∀ v ℓ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖J z (v ⊗ₜ[ℂ] ℓ)‖ ≤ C)
    (v : V ⊗[ℂ] D) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖J z v‖ ≤ C := by
  induction v using TensorProduct.inductionOn with
  | tmul v ℓ => exact h v ℓ
  | add v w hv hw =>
    obtain ⟨C, hC, hv⟩ := hv
    obtain ⟨D, hD, hw⟩ := hw
    exact ⟨C + D, add_nonneg hC hD, fun z => by
      rw [map_add]
      exact (norm_add_le _ _).trans (add_le_add (hv z) (hw z))⟩

end Additivity

end Langlands.Plancherel
