import Langlands.Representation.Plancherel.ParabolicCompositionScalar

/-! # Scalar comparison with fixed factors in the composition law -/

noncomputable section

namespace Langlands.Plancherel

section ThreeCarriers

variable {V₀ V₁ V₂ : Type*} [AddCommGroup V₀] [Module ℂ V₀]
  [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  (J₁₀ : V₀ →ₗ[ℂ] V₁) (J₀₁ : V₁ →ₗ[ℂ] V₀)
  (J₂₁ : V₁ →ₗ[ℂ] V₂) (J₁₂ : V₂ →ₗ[ℂ] V₁)
  (J₂₀ : V₀ →ₗ[ℂ] V₂) (J₀₂ : V₂ →ₗ[ℂ] V₀)
  {a b s₀₂ s₀₁ s₁₂ : ℂ}

/-- A distance-additive product with specified Haar factors gives the
corresponding factorization of its round-trip scalar. -/
theorem roundTripScalar_mul_of_scaled_composition [Nontrivial V₀]
    (hF : J₂₁.comp J₁₀ = a • J₂₀) (hR : J₀₁.comp J₁₂ = b • J₀₂)
    (h₀₂ : J₀₂.comp J₂₀ = s₀₂ • LinearMap.id)
    (h₀₁ : J₀₁.comp J₁₀ = s₀₁ • LinearMap.id)
    (h₁₂ : J₁₂.comp J₂₁ = s₁₂ • LinearMap.id) :
    a * b * s₀₂ = s₀₁ * s₁₂ := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V₀)
  apply smul_left_injective ℂ hv
  have hFv : J₂₁ (J₁₀ v) = a • J₂₀ v := LinearMap.congr_fun hF v
  have hRv : J₀₁ (J₁₂ (J₂₀ v)) = b • J₀₂ (J₂₀ v) := LinearMap.congr_fun hR (J₂₀ v)
  have h₀₂v : J₀₂ (J₂₀ v) = s₀₂ • v := LinearMap.congr_fun h₀₂ v
  have h₀₁v : J₀₁ (J₁₀ v) = s₀₁ • v := LinearMap.congr_fun h₀₁ v
  have h₁₂v : J₁₂ (J₂₁ (J₁₀ v)) = s₁₂ • J₁₀ v := LinearMap.congr_fun h₁₂ (J₁₀ v)
  calc
    _ = J₀₁ (J₁₂ (J₂₁ (J₁₀ v))) := by rw [hFv, map_smul, map_smul, hRv, h₀₂v, smul_smul, smul_smul, mul_assoc]
    _ = _ := by rw [h₁₂v, map_smul, h₀₁v, smul_smul, mul_comm s₁₂ s₀₁]

end ThreeCarriers

section FourCarriers

variable {V₀ V₁ V₂ V₃ : Type*} [AddCommGroup V₀] [Module ℂ V₀]
  [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  [AddCommGroup V₃] [Module ℂ V₃]
  (J₁₀ : V₀ →ₗ[ℂ] V₁) (J₀₂ : V₂ →ₗ[ℂ] V₀)
  (J₂₃ : V₃ →ₗ[ℂ] V₂) (J₃₁ : V₁ →ₗ[ℂ] V₃)
  (J₁₂ : V₂ →ₗ[ℂ] V₁) (J₂₁ : V₁ →ₗ[ℂ] V₂)
  (J₀₃ : V₃ →ₗ[ℂ] V₀) (J₃₀ : V₀ →ₗ[ℂ] V₃)
  {a₁₂ a₂₁ a₀₃ a₃₀ s₀ s₁ : ℂ}

/-- The four distance-additive compositions comparing two opposite pairs
compare their scalars with the corresponding products of Haar factors. -/
theorem oppositeScalar_mul_of_scaled_composition (hJ : J₁₀ ≠ 0)
    (h₁₂ : J₁₀.comp J₀₂ = a₁₂ • J₁₂) (h₂₁ : J₂₃.comp J₃₁ = a₂₁ • J₂₁)
    (h₀₃ : J₀₂.comp J₂₃ = a₀₃ • J₀₃) (h₃₀ : J₃₁.comp J₁₀ = a₃₀ • J₃₀)
    (h₀ : J₀₃.comp J₃₀ = s₀ • LinearMap.id) (h₁ : J₁₂.comp J₂₁ = s₁ • LinearMap.id) :
    a₁₂ * a₂₁ * s₁ = a₀₃ * a₃₀ * s₀ := by
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hJ
  have hv' : J₁₀ v ≠ 0 := hv
  apply smul_left_injective ℂ hv'
  have h₁₂v (w : V₂) : J₁₀ (J₀₂ w) = a₁₂ • J₁₂ w := LinearMap.congr_fun h₁₂ w
  have h₂₁v (w : V₁) : J₂₃ (J₃₁ w) = a₂₁ • J₂₁ w := LinearMap.congr_fun h₂₁ w
  have h₀₃v (w : V₃) : J₀₂ (J₂₃ w) = a₀₃ • J₀₃ w := LinearMap.congr_fun h₀₃ w
  have h₃₀v (w : V₀) : J₃₁ (J₁₀ w) = a₃₀ • J₃₀ w := LinearMap.congr_fun h₃₀ w
  have h₀v (w : V₀) : J₀₃ (J₃₀ w) = s₀ • w := LinearMap.congr_fun h₀ w
  have h₁v (w : V₁) : J₁₂ (J₂₁ w) = s₁ • w := LinearMap.congr_fun h₁ w
  calc
    (a₁₂ * a₂₁ * s₁) • J₁₀ v = J₁₀ (J₀₂ (J₂₃ (J₃₁ (J₁₀ v)))) := by
      rw [h₂₁v, map_smul, map_smul, h₁₂v, h₁v, smul_smul, smul_smul, mul_comm a₂₁ a₁₂]
    _ = (a₀₃ * a₃₀ * s₀) • J₁₀ v := by
      rw [h₃₀v, map_smul, map_smul, map_smul, h₀₃v, map_smul, h₀v, map_smul,
        smul_smul, smul_smul, mul_comm a₃₀ a₀₃]

end FourCarriers

end Langlands.Plancherel
