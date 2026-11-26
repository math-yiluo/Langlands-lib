import Langlands.Representation.Unitary.IntegratedOperator
import Mathlib.MeasureTheory.Group.Integral

/-! # Commutation and local approximation by integrated kernels -/

noncomputable section

universe uG uE

open MeasureTheory Set Filter

set_option autoImplicit false

namespace Langlands.Analysis

variable {G : Type uG} [Group G] [MeasurableSpace G]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (ν : Measure G) (π : G →* (E →L[ℂ] E))
  (hπnorm : ∀ (g : G) (v : E), ‖π g v‖ = ‖v‖)
  (hπmeas : ∀ v : E, AEStronglyMeasurable (fun g => π g v) ν)

/-- A kernel invariant under conjugation by `k` has integrated action commuting
with `π k` if both Haar translations preserve the measure. -/
theorem integratedIsometricAction_commute_conjugation [MeasurableMul G]
    [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant]
    (h : G → ℂ) (hh : Integrable h ν) (k : G) (hConj : ∀ g, h (k⁻¹ * g * k) = h g) (v : E) :
    π k (integratedIsometricAction ν π hπnorm hπmeas h hh v) =
      integratedIsometricAction ν π hπnorm hπmeas h hh (π k v) := by
  simp only [integratedIsometricAction_apply]
  rw [← (π k).integral_comp_comm (isometricActionIntegrand_integrable ν π hπnorm hπmeas h hh v)]
  calc
    (∫ g, π k (h g • π g v) ∂ν) = ∫ g, h g • π (k * g) v ∂ν := by
      apply integral_congr_ae (Eventually.of_forall fun g => ?_)
      simp [map_smul, map_mul]
    _ = ∫ g, h (k⁻¹ * g * k) • π (k * (k⁻¹ * g * k)) v ∂ν :=
      ((integral_mul_left_eq_self (μ := ν) (fun g => h (g * k) • π (k * (g * k)) v) k⁻¹).trans
        (integral_mul_right_eq_self (μ := ν) (fun g => h g • π (k * g) v) k)).symm
    _ = ∫ g, h g • π g (π k v) ∂ν := by
      apply integral_congr_ae (Eventually.of_forall fun g => ?_)
      rw [hConj, ← mul_assoc k (k⁻¹ * g) k, ← mul_assoc k k⁻¹ g]
      simp [map_mul]

/-- The approximation error of a nonnegative real kernel of integral one is
bounded by an orbit error bound on its support. -/
theorem integratedIsometricAction_sub_le_of_nonnegative
    (h : G → ℝ) (hh : Integrable h ν) (hnonneg : ∀ g, 0 ≤ h g) (hmass : ∫ g, h g ∂ν = 1)
    (v : E) (ε : ℝ) (hSupport : ∀ g ∈ Function.support h, ‖π g v - v‖ ≤ ε) :
    ‖integratedIsometricAction ν π hπnorm hπmeas (fun g => (h g : ℂ)) hh.ofReal v - v‖ ≤ ε := by
  have hconst : (∫ g, (h g : ℂ) • v ∂ν) = v := by
    rw [integral_smul_const, integral_complex_ofReal, hmass]
    simp
  have herror :
      integratedIsometricAction ν π hπnorm hπmeas (fun g => (h g : ℂ)) hh.ofReal v - v =
        ∫ g, (h g : ℂ) • (π g v - v) ∂ν := by
    calc
      _ = (∫ g, (h g : ℂ) • π g v ∂ν) - ∫ g, (h g : ℂ) • v ∂ν := by
        rw [integratedIsometricAction_apply, hconst]
      _ = _ := by
        simp_rw [smul_sub]
        exact (integral_sub (isometricActionIntegrand_integrable ν π hπnorm hπmeas _ hh.ofReal v)
          (hh.ofReal.smul_const v)).symm
  rw [herror]
  calc
    ‖∫ g, (h g : ℂ) • (π g v - v) ∂ν‖ ≤ ∫ g, h g * ε ∂ν := by
      apply norm_integral_le_of_norm_le (hh.mul_const ε)
      refine Eventually.of_forall fun g => ?_
      by_cases hg : h g = 0
      · simp [hg]
      · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (hnonneg g)]
        exact mul_le_mul_of_nonneg_left (hSupport g hg) (hnonneg g)
    _ = ε := by rw [integral_mul_const, hmass, one_mul]

/-- Conjugation-invariant integrated operators commute with the corresponding
translation, and probability kernels satisfy the local orbit approximation bound. -/
def IntegratedKernelLocalApproximationStatement : Prop :=
  (∀ [MeasurableMul G] [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant]
    (h : G → ℂ) (hh : Integrable h ν) (k : G), (∀ g, h (k⁻¹ * g * k) = h g) → ∀ v : E,
      π k (integratedIsometricAction ν π hπnorm hπmeas h hh v) =
        integratedIsometricAction ν π hπnorm hπmeas h hh (π k v)) ∧
  (∀ (h : G → ℝ) (hh : Integrable h ν), (∀ g, 0 ≤ h g) → (∫ g, h g ∂ν) = 1 →
    ∀ (v : E) (ε : ℝ), (∀ g ∈ Function.support h, ‖π g v - v‖ ≤ ε) →
      ‖integratedIsometricAction ν π hπnorm hπmeas (fun g => (h g : ℂ)) hh.ofReal v - v‖ ≤ ε)

theorem integratedKernelLocalApproximation : IntegratedKernelLocalApproximationStatement ν π hπnorm hπmeas := by
  refine ⟨?_, integratedIsometricAction_sub_le_of_nonnegative ν π hπnorm hπmeas⟩
  intro _ _ _ h hh k
  exact integratedIsometricAction_commute_conjugation ν π hπnorm hπmeas h hh k

end Langlands.Analysis
