import Langlands.Geometry.Analytic.TateGaussPoint
import Langlands.Geometry.Analytic.TateSeries

/-! # Separating the finite dominant part of an actual Tate series -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTateAlgebra

variable {σ : Type u} {A : Type v} [NormedCommRing A] [IsUltrametricDist A]

/-- The actual finite sum of the selected coefficient monomials. -/
def coefficientPart (f : StrictTateAlgebra σ A) (S : Finset (σ →₀ ℕ)) :
    StrictTateAlgebra σ A :=
  ∑ d ∈ S, monomial σ A d (MvPowerSeries.coeff d (series σ A f))

theorem coeff_coefficientPart [DecidableEq σ]
    (f : StrictTateAlgebra σ A) (S : Finset (σ →₀ ℕ))
    (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (series σ A (coefficientPart f S)) =
      if d ∈ S then MvPowerSeries.coeff d (series σ A f) else 0 := by
  classical
  change coefficientCLM σ A d (∑ e ∈ S,
    monomial σ A e (MvPowerSeries.coeff e (series σ A f))) = _
  simp only [map_sum, coefficient_monomial]
  exact Finset.sum_ite_eq S d (fun x => MvPowerSeries.coeff x (series σ A f))

theorem norm_coefficientPart_le (f : StrictTateAlgebra σ A)
    (S : Finset (σ →₀ ℕ)) : ‖coefficientPart f S‖ ≤ ‖f‖ := by
  classical
  apply (norm_le_iff σ A _ (norm_nonneg f)).mpr
  intro d
  rw [coeff_coefficientPart]
  split_ifs
  · exact norm_coeff_le σ A f d
  · simpa only [norm_zero] using norm_nonneg f

/-- The remainder is uniformly strictly small, using attainment of its
coefficient supremum. Pointwise strict inequalities alone are not substituted
for this argument. -/
theorem norm_sub_coefficientPart_lt (f : StrictTateAlgebra σ A)
    (S : Finset (σ →₀ ℕ)) {ε : ℝ} (hε : 0 < ε)
    (hS : ∀ d, ε ≤ ‖MvPowerSeries.coeff d (series σ A f)‖ → d ∈ S) :
    ‖f - coefficientPart f S‖ < ε := by
  classical
  obtain ⟨d, hd⟩ := exists_norm_coeff_eq (f - coefficientPart f S)
  rw [← hd]
  change ‖MvPowerSeries.coeff d
    (series σ A f - series σ A (coefficientPart f S))‖ < ε
  rw [map_sub, coeff_coefficientPart]
  by_cases hmem : d ∈ S
  · simp only [hmem, ↓reduceIte, sub_self, norm_zero]
    exact hε
  · simp only [hmem, ↓reduceIte, sub_zero]
    exact lt_of_not_ge (fun h => hmem (hS d h))

/-- The selected exponents are constructed from the actual coefficients and
the proved finiteness of positive superlevel sets. -/
def dominantExponents (f : StrictTateAlgebra σ A) {ε : ℝ} (hε : 0 < ε) :
    Finset (σ →₀ ℕ) :=
  (finite_coeff_norm_ge f hε).toFinset

@[simp]
theorem mem_dominantExponents (f : StrictTateAlgebra σ A) {ε : ℝ}
    (hε : 0 < ε) (d : σ →₀ ℕ) :
    d ∈ dominantExponents f hε ↔
      ε ≤ ‖MvPowerSeries.coeff d (series σ A f)‖ :=
  Set.Finite.mem_toFinset _

theorem norm_sub_dominantPart_lt (f : StrictTateAlgebra σ A)
    {ε : ℝ} (hε : 0 < ε) :
    ‖f - coefficientPart f (dominantExponents f hε)‖ < ε :=
  norm_sub_coefficientPart_lt f _ hε
    (fun d hd => (mem_dominantExponents f hε d).mpr hd)

/-- For a nonzero series, the finite part at its own norm is nonempty. -/
theorem dominantExponents_nonempty (f : StrictTateAlgebra σ A) (hf : f ≠ 0) :
    (dominantExponents f (norm_pos_iff.mpr hf)).Nonempty := by
  obtain ⟨d, hd⟩ := exists_norm_coeff_eq f
  exact ⟨d, (mem_dominantExponents f _ d).mpr hd.ge⟩

end Langlands.Analytic.StrictTateAlgebra
