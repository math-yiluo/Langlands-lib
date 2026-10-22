import Langlands.Geometry.Analytic.RestrictedSeriesDefinitions
import Mathlib.RingTheory.PowerSeries.Restricted
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Analysis.Polynomial.Norm

/-! # Polynomial approximation in the one-variable Tate algebra -/

noncomputable section

universe u

namespace Langlands.Analytic

open Filter
open scoped Topology

namespace RestrictedSeries

variable (A : Type u) [NormedCommRing A] [IsUltrametricDist A]

theorem coeff_tendsto_zero (f : Algebra A) :
    Tendsto (fun n => coeff A n f) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := (PowerSeries.isRestricted_iff' 1 f.val).mp f.property
  simpa only [coeff_apply, one_pow, mul_one] using h

@[simp]
theorem coeff_ofPolynomial (p : Polynomial A) (n : ℕ) :
    coeff A n (ofPolynomial A p) = p.coeff n :=
  Polynomial.coeff_coe p n

theorem ofPolynomial_injective : Function.Injective (ofPolynomial A) := by
  intro p q h
  apply Polynomial.ext
  intro n
  simpa only [coeff_ofPolynomial] using congrArg (coeff A n) h

theorem norm_le_iff (f : Algebra A) {C : ℝ} (hC : 0 ≤ C) :
    ‖f‖ ≤ C ↔ ∀ n, ‖coeff A n f‖ ≤ C := by
  rw [StrictTateAlgebra.norm_le_iff Unit A f hC]
  constructor
  · intro h n
    exact h (Finsupp.single () n)
  · intro h t
    simpa only [coeff_apply, PowerSeries.coeff_def (s := t) rfl,
      StrictTateAlgebra.series] using h (t ())

/-- The polynomial coefficient supremum norm is precisely the restricted-series
norm under the actual inclusion. -/
theorem norm_ofPolynomial (p : Polynomial A) :
    ‖ofPolynomial A p‖ = p.supNorm := by
  apply le_antisymm
  · apply (norm_le_iff A _ p.supNorm_nonneg).mpr
    simpa only [coeff_ofPolynomial] using p.le_supNorm
  · obtain ⟨n, hn⟩ := p.exists_eq_supNorm
    rw [hn]
    simpa only [coeff_ofPolynomial] using
      (norm_le_iff A (ofPolynomial A p) (norm_nonneg _)).mp le_rfl n

/-- Truncate the genuine power series to a polynomial. -/
def trunc (n : ℕ) (f : Algebra A) : Polynomial A :=
  PowerSeries.trunc n f.val

theorem coeff_trunc (n m : ℕ) (f : Algebra A) :
    (trunc A n f).coeff m = if m < n then coeff A m f else 0 :=
  PowerSeries.coeff_trunc m n f.val

theorem norm_trunc_le (n : ℕ) (f : Algebra A) :
    ‖ofPolynomial A (trunc A n f)‖ ≤ ‖f‖ := by
  apply (norm_le_iff A _ (norm_nonneg f)).mpr
  intro m
  rw [coeff_ofPolynomial, coeff_trunc]
  split_ifs
  · exact (norm_le_iff A f (norm_nonneg f)).mp le_rfl m
  · simp

/-- Polynomial truncations converge in the Gauss norm, not just in the formal
coefficient topology. No completeness assumption is needed. -/
theorem tendsto_trunc (f : Algebra A) :
    Tendsto (fun n => ofPolynomial A (trunc A n f)) atTop (𝓝 f) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (coeff_tendsto_zero A f)
    (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply (norm_le_iff A _ (le_of_lt (half_pos hε))).mpr
  intro m
  rw [map_sub, coeff_ofPolynomial, coeff_trunc]
  split_ifs with hm
  · simp only [sub_self, norm_zero]
    exact le_of_lt (half_pos hε)
  · simpa only [zero_sub, norm_neg, dist_zero_right] using
      (hN m (hn.trans (Nat.le_of_not_gt hm))).le

theorem denseRange_ofPolynomial : DenseRange (ofPolynomial A) := by
  intro f
  exact mem_closure_of_tendsto (tendsto_trunc A f)
    (Filter.Eventually.of_forall fun n => ⟨trunc A n f, rfl⟩)

end RestrictedSeries

end Langlands.Analytic
