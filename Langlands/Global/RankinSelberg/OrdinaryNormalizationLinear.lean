import Langlands.Global.RankinSelberg.OrdinaryNormalizationUniqueness

/-! # Linearity of entire ordinary integral normalizations -/

noncomputable section

open MeasureTheory Set

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

variable {V X : Type*} [AddCommGroup V] [Module ℂ V] [MeasurableSpace X]

/-- For a linear family of integrands with convergence on right half-planes, whole-plane
normalization by an eventually nonzero scalar factor is linear. -/
def OrdinaryNormalizationLinearStatement : Prop :=
  ∀ (μ : Measure X) (K : V →ₗ[ℂ] (ℂ → X → ℂ)) (L : ℂ → ℂ),
    (∃ b : ℝ, ∀ s : ℂ, b < s.re → L s ≠ 0) →
    (∀ v, ∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable (K v s) μ) →
    ∀ N : ∀ v, OrdinaryIntegralNormalization (fun s => ∫ x, K v s x ∂μ) L,
      ∃ A : V →ₗ[ℂ] (ℂ → ℂ), ∀ v, A v = (N v).value

/-- Linearity follows from the linearity of the absolutely convergent integrals and uniqueness
of the entire normalization. -/
theorem ordinaryNormalizationLinear : OrdinaryNormalizationLinearStatement (V := V) (X := X) := by
  intro μ K L hL hI N
  refine ⟨{ toFun := fun v => (N v).value
            map_add' := ?_
            map_smul' := ?_ }, fun _ => rfl⟩
  · intro v w
    obtain ⟨bv, hv⟩ := hI v
    obtain ⟨bw, hw⟩ := hI w
    obtain ⟨cv, hNv⟩ := (N v).eq_on_right
    obtain ⟨cw, hNw⟩ := (N w).eq_on_right
    let M : OrdinaryIntegralNormalization (fun s => ∫ x, K (v + w) s x ∂μ) L :=
      ⟨(N v).value + (N w).value, (N v).analytic.add (N w).analytic,
        max (max bv bw) (max cv cw), fun s hs => by
          have h₁ := (le_max_left (max bv bw) (max cv cw)).trans_lt hs
          have h₂ := (le_max_right (max bv bw) (max cv cw)).trans_lt hs
          simp only [map_add, Pi.add_apply]
          rw [integral_add (hv s ((le_max_left bv bw).trans_lt h₁))
            (hw s ((le_max_right bv bw).trans_lt h₁)),
            hNv s ((le_max_left cv cw).trans_lt h₂), hNw s ((le_max_right cv cw).trans_lt h₂), add_mul]⟩
    exact (N (v + w)).value_eq_of_factor_ne_zero M hL
  · intro c v
    obtain ⟨bv, hv⟩ := (N v).eq_on_right
    let M : OrdinaryIntegralNormalization (fun s => ∫ x, K (c • v) s x ∂μ) L :=
      ⟨c • (N v).value, analyticOnNhd_const.mul (N v).analytic, bv, fun s hs => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, integral_const_mul, hv s hs, mul_assoc]⟩
    exact (N (c • v)).value_eq_of_factor_ne_zero M hL

end Langlands.Global.RankinSelbergGlobal
