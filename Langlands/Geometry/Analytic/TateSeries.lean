import Langlands.Geometry.Analytic.TateSeries.Statement

/-! # Norm-convergent monomial expansion in the strict Tate algebra -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTateAlgebra

open Filter
open scoped Topology ZeroAtInfty

variable (σ : Type u) (K : Type v) [NormedCommRing K] [IsUltrametricDist K]

/-- The family of coefficient monomials tends to zero in the Gauss norm. -/
theorem monomials_tendsto_zero (f : StrictTateAlgebra σ K) :
    Tendsto (fun d => monomial σ K d (MvPowerSeries.coeff d (series σ K f)))
      cofinite (𝓝 0) := by
  have h := zero_at_infty (coefficients σ K f)
  rw [Filter.cocompact_eq_cofinite] at h
  change Tendsto (fun d : σ →₀ ℕ => MvPowerSeries.coeff d (series σ K f))
    cofinite (𝓝 0) at h
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [norm_monomial] using tendsto_zero_iff_norm_tendsto_zero.mp h

variable [CompleteSpace K]

theorem summable_monomials (f : StrictTateAlgebra σ K) :
    Summable (fun d => monomial σ K d (MvPowerSeries.coeff d (series σ K f))) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (monomials_tendsto_zero σ K f)

/-- The coefficient monomial sum is the original restricted power series,
with convergence in its Banach norm. -/
theorem tsum_monomials (f : StrictTateAlgebra σ K) :
    (∑' d, monomial σ K d (MvPowerSeries.coeff d (series σ K f))) = f := by
  classical
  apply Subtype.ext
  apply MvPowerSeries.ext
  intro e
  change coefficientCLM σ K e (∑' d, monomial σ K d
    (MvPowerSeries.coeff d (series σ K f))) = _
  rw [(coefficientCLM σ K e).map_tsum (summable_monomials σ K f)]
  simp only [coefficient_monomial, tsum_ite_eq', series]

/-- Finite partial sums of the genuine monomials converge to every Tate series. -/
theorem hasSum_monomials (f : StrictTateAlgebra σ K) :
    HasSum (fun d => monomial σ K d (MvPowerSeries.coeff d (series σ K f))) f := by
  have h := (summable_monomials σ K f).hasSum
  rw [tsum_monomials] at h
  exact h

/-- Every restricted series is its norm-convergent monomial expansion. -/
theorem monomialExpansion : MonomialExpansionStatement.{u, v} := by
  intro σ K _ _ _ f
  exact hasSum_monomials σ K f

end Langlands.Analytic.StrictTateAlgebra
