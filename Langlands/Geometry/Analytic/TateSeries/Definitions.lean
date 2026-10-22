import Langlands.Geometry.Analytic.TateAlgebra
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Analysis.Normed.Operator.Basic

/-! # Monomials and bounded coefficient extraction in the strict Tate algebra -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTateAlgebra

open Filter
open scoped Topology ZeroAtInfty

variable (σ : Type u) (K : Type v) [NormedCommRing K] [IsUltrametricDist K]

/-- The actual restricted monomial with exponent `d` and coefficient `a`. -/
def monomial (d : σ →₀ ℕ) (a : K) : StrictTateAlgebra σ K :=
  ⟨MvPowerSeries.monomial d a, MvPowerSeries.isRestricted_monomial _ d a⟩

/-- Coefficient extraction is a bounded linear map for the Gauss norm. -/
def coefficientCLM (d : σ →₀ ℕ) : StrictTateAlgebra σ K →L[K] K :=
  ((MvPowerSeries.coeff d).comp (restrictedSubalgebra σ K).val.toLinearMap).mkContinuous
    1 (fun f => by
      rw [one_mul]
      change ‖MvPowerSeries.coeff d (series σ K f)‖ ≤ ‖f‖
      exact norm_coeff_le σ K f d)

@[simp]
theorem coefficientCLM_apply (d : σ →₀ ℕ) (f : StrictTateAlgebra σ K) :
    coefficientCLM σ K d f = MvPowerSeries.coeff d (series σ K f) := rfl

theorem coefficient_monomial [DecidableEq σ] (d e : σ →₀ ℕ) (a : K) :
    coefficientCLM σ K d (monomial σ K e a) = if d = e then a else 0 :=
  MvPowerSeries.coeff_monomial d e a

theorem norm_monomial (d : σ →₀ ℕ) (a : K) :
    ‖monomial σ K d a‖ = ‖a‖ := by
  classical
  apply le_antisymm
  · apply (norm_le_iff σ K _ (norm_nonneg a)).mpr
    intro e
    change ‖MvPowerSeries.coeff e (MvPowerSeries.monomial d a)‖ ≤ ‖a‖
    rw [MvPowerSeries.coeff_monomial]
    split_ifs <;> simp
  · have h := norm_coeff_le σ K (monomial σ K d a) d
    change ‖MvPowerSeries.coeff d (MvPowerSeries.monomial d a)‖ ≤ _ at h
    simpa using h

end Langlands.Analytic.StrictTateAlgebra
