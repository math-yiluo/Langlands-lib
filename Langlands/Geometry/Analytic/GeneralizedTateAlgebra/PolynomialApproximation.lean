import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.PolynomialApproximationStatement
import Mathlib.Order.Filter.AtTopBot.Finset

/-! # Polynomial approximation in positive-polyradius Tate algebras -/

noncomputable section

open Filter
open scoped Topology Classical

universe u v

namespace Langlands.Analytic.GeneralizedTateAlgebra

variable {σ : Type u} (r : PositivePolyradius σ) (K : Type v)
  [NormedCommRing K] [IsUltrametricDist K]

/-- The inclusion into formal power series, as an algebra homomorphism. -/
def seriesAlgHom : GeneralizedTateAlgebra r K →ₐ[K] MvPowerSeries σ K :=
  (weightedRestrictedSubalgebra r K).val

@[simp] theorem seriesAlgHom_apply (f : GeneralizedTateAlgebra r K) :
    seriesAlgHom r K f = series r K f := rfl

/-- Polynomial evaluation at the actual coordinate monomials. -/
def polynomialMap : MvPolynomial σ K →ₐ[K] GeneralizedTateAlgebra r K :=
  MvPolynomial.aeval (fun i => monomial r K (Finsupp.single i 1) (1 : K))

/-- Coordinate evaluation agrees with the usual polynomial-to-series inclusion. -/
theorem series_polynomialMap (p : MvPolynomial σ K) :
    series r K (polynomialMap r K p) = (p : MvPowerSeries σ K) := by
  have h : (seriesAlgHom r K).comp (polynomialMap r K) =
      MvPolynomial.coeToMvPowerSeries.algHom K := by
    ext i : 1
    change series r K (MvPolynomial.aeval
      (fun j => monomial r K (Finsupp.single j 1) (1 : K)) (MvPolynomial.X i)) = _
    rw [MvPolynomial.aeval_X]
    simp [series, monomial, MvPowerSeries.X]
  simpa using DFunLike.congr_fun h p

@[simp] theorem coeff_polynomialMap (p : MvPolynomial σ K) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (series r K (polynomialMap r K p)) = p.coeff d := by
  rw [series_polynomialMap, MvPolynomial.coeff_coe]

@[simp] theorem polynomialMap_monomial (d : σ →₀ ℕ) (a : K) :
    polynomialMap r K (MvPolynomial.monomial d a) = monomial r K d a := by
  apply Subtype.ext
  change series r K (polynomialMap r K _) = _
  rw [series_polynomialMap, MvPolynomial.coe_monomial]
  rfl

/-- Retain the coefficients indexed by the finite set `s`. -/
def truncation (s : Finset (σ →₀ ℕ)) (f : GeneralizedTateAlgebra r K) :
    GeneralizedTateAlgebra r K :=
  ∑ d ∈ s, monomial r K d (MvPowerSeries.coeff d (series r K f))

@[simp] theorem coeff_truncation (s : Finset (σ →₀ ℕ))
    (f : GeneralizedTateAlgebra r K) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (series r K (truncation r K s f)) =
      if d ∈ s then MvPowerSeries.coeff d (series r K f) else 0 := by
  classical
  change MvPowerSeries.coeff d (seriesAlgHom r K (∑ e ∈ s, _)) = _
  simp [map_sum, coeff_monomial]

/-- A uniform weighted bound on omitted coefficients bounds the whole remainder. -/
theorem norm_truncation_sub_le (s : Finset (σ →₀ ℕ))
    (f : GeneralizedTateAlgebra r K) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ d ∉ s, ‖MvPowerSeries.coeff d (series r K f)‖ * r.weight d ≤ ε) :
    ‖truncation r K s f - f‖ ≤ ε := by
  classical
  apply (norm_le_iff r K _ hε).mpr
  intro d
  change ‖MvPowerSeries.coeff d (seriesAlgHom r K (truncation r K s f - f))‖ *
    r.weight d ≤ ε
  rw [map_sub, map_sub, seriesAlgHom_apply, seriesAlgHom_apply, coeff_truncation]
  split_ifs with hd
  · simpa using hε
  · simpa using h d hd

/-- Finite monomial truncations converge in the weighted Gauss norm. -/
theorem tendsto_truncation (f : GeneralizedTateAlgebra r K) :
    Tendsto (fun s => truncation r K s f) atTop (𝓝 f) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hdecay : Tendsto
      (fun d => ‖MvPowerSeries.coeff d (series r K f)‖ * r.weight d) cofinite (𝓝 0) :=
    f.property
  have hevent := (Metric.tendsto_nhds.mp hdecay) (ε / 2) (half_pos hε)
  have hfinite := eventually_cofinite.mp hevent
  refine ⟨hfinite.toFinset, fun s hs => ?_⟩
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (norm_truncation_sub_le r K s f (half_pos hε).le ?_)
    (half_lt_self hε)
  intro d hd
  have hnot : d ∉ hfinite.toFinset := fun hmem => hd (hs hmem)
  have hsmall : dist (‖MvPowerSeries.coeff d (series r K f)‖ * r.weight d) 0 < ε / 2 := by
    simpa using hnot
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg
    (mul_nonneg (norm_nonneg _) (r.weight_pos d).le)] using hsmall.le

/-- Every element is the unconditional sum of its actual coefficient monomials. -/
theorem hasSum_monomials (f : GeneralizedTateAlgebra r K) :
    HasSum (fun d => monomial r K d (MvPowerSeries.coeff d (series r K f))) f :=
  tendsto_truncation r K f

/-- Each finite truncation is the evaluation of the polynomial with those coefficients. -/
theorem polynomialMap_sum_monomials (s : Finset (σ →₀ ℕ))
    (f : GeneralizedTateAlgebra r K) :
    polynomialMap r K
      (∑ d ∈ s, MvPolynomial.monomial d (MvPowerSeries.coeff d (series r K f))) =
        truncation r K s f := by
  simp [truncation, map_sum]

/-- Coordinate polynomial evaluation has dense range without completeness hypotheses. -/
theorem denseRange_polynomialMap : DenseRange (polynomialMap r K) := by
  intro f
  apply mem_closure_of_tendsto (tendsto_truncation r K f)
  exact Eventually.of_forall fun s => ⟨_, polynomialMap_sum_monomials r K s f⟩

/-- The complete published monomial-expansion and polynomial-density target. -/
theorem polynomialApproximation : PolynomialApproximationStatement r K :=
  ⟨hasSum_monomials r K, denseRange_polynomialMap r K⟩

end Langlands.Analytic.GeneralizedTateAlgebra
