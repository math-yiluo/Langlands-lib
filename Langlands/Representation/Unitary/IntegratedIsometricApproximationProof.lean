import Langlands.Representation.Unitary.IntegratedIsometricApproximationStatement

noncomputable section

namespace Langlands.Analysis

open MeasureTheory Filter
open scoped Topology

universe uG uE

/-- Normalize the weighted constant integral and estimate the orbit error on
the eventual shrinking support. -/
theorem integratedIsometricApproximation :
    IntegratedIsometricApproximationStatement.{uG, uE} := by
  intro G _ _ _ E _ _ _ μ π hπnorm hπmeas hπcont f hf hnonneg hmass hsupport x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hnear : {g : G | ‖π g x - x‖ < ε / 2} ∈ 𝓝 (1 : G) := by
    change ∀ᶠ g in 𝓝 (1 : G), ‖π g x - x‖ < ε / 2
    simpa only [map_one, one_apply_eq_self, dist_eq_norm] using
      Metric.continuousAt_iff'.mp (hπcont x) (ε / 2) hε2
  filter_upwards [hsupport _ hnear] with n hn
  have hconst : (∫ g, (f n g : ℂ) • x ∂μ) = x := by
    rw [integral_smul_const, integral_complex_ofReal, hmass n]
    simp
  have herror :
      integratedIsometricAction μ π hπnorm hπmeas
        (fun g => (f n g : ℂ)) (hf n).ofReal x - x =
        ∫ g, (f n g : ℂ) • (π g x - x) ∂μ := by
    calc
      integratedIsometricAction μ π hπnorm hπmeas
          (fun g => (f n g : ℂ)) (hf n).ofReal x - x =
          (∫ g, (f n g : ℂ) • π g x ∂μ) -
            ∫ g, (f n g : ℂ) • x ∂μ := by
              rw [integratedIsometricAction_apply, hconst]
      _ = ∫ g, ((f n g : ℂ) • π g x - (f n g : ℂ) • x) ∂μ :=
        (integral_sub
          (isometricActionIntegrand_integrable μ π hπnorm hπmeas
            (fun g => (f n g : ℂ)) (hf n).ofReal x)
          ((hf n).ofReal.smul_const x)).symm
      _ = ∫ g, (f n g : ℂ) • (π g x - x) ∂μ := by
        simp_rw [smul_sub]
  have hbound (g : G) :
      ‖(f n g : ℂ) • (π g x - x)‖ ≤ f n g * (ε / 2) := by
    by_cases hz : f n g = 0
    · simp [hz]
    · have hsmall : ‖π g x - x‖ < ε / 2 := hn hz
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (hnonneg n g)]
      exact mul_le_mul_of_nonneg_left hsmall.le (hnonneg n g)
  rw [dist_eq_norm, herror]
  calc
    ‖∫ g, (f n g : ℂ) • (π g x - x) ∂μ‖ ≤ ∫ g, f n g * (ε / 2) ∂μ :=
      norm_integral_le_of_norm_le ((hf n).mul_const (ε / 2))
        (Eventually.of_forall hbound)
    _ = ε / 2 := by rw [integral_mul_const, hmass n, one_mul]
    _ < ε := half_lt_self hε

end Langlands.Analysis
