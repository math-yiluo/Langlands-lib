import Langlands.Analysis.WeightedL2FactorialAnalyticityStatement
import Langlands.Analysis.LocalSobolevPointwise
import Langlands.Analysis.FactorialDerivativeAnalyticity

/-! # Analyticity from weighted factorial L² derivative bounds -/

noncomputable section
open MeasureTheory Metric Set
open scoped BigOperators ContDiff
set_option autoImplicit false

namespace Langlands.Analysis

/-- Selecting the half-radius term in the weighted supremum gives factorial
L² bounds on one fixed ball. -/
theorem fixedBall_factorial_bound_of_weighted
    {d : ℕ} {F : EuclideanSpace ℝ (Fin d) → ℂ}
    {x₀ : EuclideanSpace ℝ (Fin d)} {R C A : ℝ} (hR : 0 < R)
    (hweighted : ∀ k : ℕ,
      (⨆ ρ ∈ Ico (R / 2) R,
        ENNReal.ofReal ((R - ρ) ^ k) *
          eLpNorm (fun y => euclideanBasisWordNorm (iteratedFDeriv ℝ k F y))
            2 (volume.restrict (ball x₀ ρ))) ≤
        ENNReal.ofReal (C * A ^ k * Nat.factorial k)) :
    ∀ k : ℕ,
      eLpNorm (fun y => euclideanBasisWordNorm (iteratedFDeriv ℝ k F y))
          2 (volume.restrict (ball x₀ (R / 2))) ≤
        ENNReal.ofReal (C * (A / (R / 2)) ^ k * Nat.factorial k) := by
  intro k
  have hhalf : 0 < R / 2 := by linarith
  have hmem : R / 2 ∈ Ico (R / 2) R := ⟨le_rfl, by linarith⟩
  have hsub : R - R / 2 = R / 2 := by ring
  have hselect :
      ENNReal.ofReal ((R / 2) ^ k) *
        eLpNorm (fun y => euclideanBasisWordNorm (iteratedFDeriv ℝ k F y))
          2 (volume.restrict (ball x₀ (R / 2))) ≤
        ENNReal.ofReal (C * A ^ k * Nat.factorial k) := by
    have hraw :
        ENNReal.ofReal ((R - R / 2) ^ k) *
          eLpNorm (fun y => euclideanBasisWordNorm (iteratedFDeriv ℝ k F y))
            2 (volume.restrict (ball x₀ (R / 2))) ≤
          ENNReal.ofReal (C * A ^ k * Nat.factorial k) :=
      (le_iSup_of_le (R / 2)
        (le_iSup (fun _ : R / 2 ∈ Ico (R / 2) R =>
          ENNReal.ofReal ((R - R / 2) ^ k) *
            eLpNorm (fun y => euclideanBasisWordNorm (iteratedFDeriv ℝ k F y))
              2 (volume.restrict (ball x₀ (R / 2)))) hmem)).trans (hweighted k)
    simpa only [hsub] using hraw
  have hpow : 0 < (R / 2) ^ k := pow_pos hhalf k
  have hcancel := (ENNReal.mul_le_iff_le_inv
    (ne_of_gt (ENNReal.ofReal_pos.mpr hpow)) ENNReal.ofReal_ne_top).mp hselect
  rw [← ENNReal.ofReal_inv_of_pos hpow,
    ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hpow))] at hcancel
  have hconstant : ((R / 2) ^ k)⁻¹ * (C * A ^ k * (Nat.factorial k : ℝ)) =
      C * (A / (R / 2)) ^ k * Nat.factorial k := by
    have hdiv : (A / (R / 2)) ^ k = A ^ k * ((R / 2) ^ k)⁻¹ :=
      (div_pow A (R / 2) k).trans (div_eq_mul_inv _ _)
    rw [hdiv]
    ring
  rwa [hconstant] at hcancel

/-- Weighted factorial L² control of the complete ordered derivative tensors
implies real analyticity at the centre, in every dimension. -/
theorem weightedL2FactorialAnalyticity (d : ℕ) :
    WeightedL2FactorialAnalyticityStatement d := by
  intro F x₀ R C A hR hF hweighted
  have hhalf : 0 < R / 2 := by linarith
  have hFhalf : ContDiffOn ℝ ∞ F (ball x₀ (R / 2)) :=
    hF.mono (ball_subset_ball (by linarith))
  have hL2 := fixedBall_factorial_bound_of_weighted hR hweighted
  obtain ⟨C', M', hpointwise⟩ :=
    exists_norm_iteratedFDeriv_le_factorial_of_eLpNorm_euclideanBasisWordNorm_le
      hhalf hFhalf hL2
  exact analyticAt_of_iteratedFDeriv_le_factorial
    (by positivity : 0 < R / 2 / 2)
    (hFhalf.mono (ball_subset_ball (by linarith))) hpointwise

end Langlands.Analysis
