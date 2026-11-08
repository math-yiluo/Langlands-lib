import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Complex.Basic

/-!
# Uniqueness of coefficients of convergent power series

If `Σ d_n r^n` converges absolutely for some `r > 0` and `Σ d_n X^n = 0` for all nonzero `X`
with `‖X‖ < r`, then every `d_n` vanishes. Consequently a series with `Σ b_n X^n = c X^k` on a
punctured disc has `b_n = c` for `n = k` and `0` otherwise.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open FormalMultilinearSeries Filter Topology

/-- Coefficients of an absolutely convergent power series vanishing on a punctured disc
are zero. -/
theorem coeff_eq_zero_of_tsum_eq_zero {d : ℕ → ℂ} {r : NNReal} (hr : 0 < r)
    (hsumm : Summable fun n => ‖d n‖ * (r : ℝ) ^ n)
    (hzero : ∀ X : ℂ, X ≠ 0 → ‖X‖ < r → ∑' n, d n * X ^ n = 0) : ∀ n, d n = 0 := by
  set p : FormalMultilinearSeries ℂ ℂ ℂ := ofScalars ℂ d with hp
  have hnorm : ∀ n, ‖p n‖ = ‖d n‖ := fun n => ofScalars_norm (E := ℂ) d n
  have hrad : (r : ENNReal) ≤ p.radius :=
    p.le_radius_of_summable_norm (by simpa [hnorm] using hsumm)
  have hpos : 0 < p.radius := lt_of_lt_of_le (by exact_mod_cast hr) hrad
  have hps : HasFPowerSeriesAt p.sum p 0 := (p.hasFPowerSeriesOnBall hpos).hasFPowerSeriesAt
  have hp0 : p = 0 := by
    by_contra hne
    have hev := hps.locally_ne_zero hne
    have hball : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖z‖ < r := by
      have : Metric.ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ (by exact_mod_cast hr)
      filter_upwards [nhdsWithin_le_nhds this] with z hz
      simpa using hz
    obtain ⟨z, hz1, hz2, hz3⟩ := (hev.and (hball.and self_mem_nhdsWithin)).exists
    apply hz1
    rw [show p.sum z = ofScalarsSum d z from rfl, ofScalars_sum_eq]
    simpa [smul_eq_mul, mul_comm] using hzero z hz3 hz2
  intro n
  have := (ofScalars_series_eq_zero (E := ℂ) (c := d)).mp hp0
  exact congrFun this n

/-- If `Σ b_n X^n = c X^k` on a punctured disc and the series converges absolutely there,
then `b_n = c` for `n = k` and `b_n = 0` otherwise. -/
theorem coeff_eq_of_tsum_eq_monomial {b : ℕ → ℂ} {r : NNReal} (hr : 0 < r)
    (hsumm : Summable fun n => ‖b n‖ * (r : ℝ) ^ n) (c : ℂ) (k : ℕ)
    (hval : ∀ X : ℂ, X ≠ 0 → ‖X‖ < r → ∑' n, b n * X ^ n = c * X ^ k) :
    ∀ n, b n = if n = k then c else 0 := by
  set d : ℕ → ℂ := fun n => b n - if n = k then c else 0 with hd
  have hsumm' : Summable fun n => ‖d n‖ * (r : ℝ) ^ n := by
    have hfin : Summable fun n => ‖(if n = k then c else 0 : ℂ)‖ * (r : ℝ) ^ n := by
      apply summable_of_ne_finset_zero (s := {k})
      intro n hn
      simp only [Finset.mem_singleton] at hn
      simp [hn]
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hsumm.add hfin)
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (by positivity)
  have hzero : ∀ X : ℂ, X ≠ 0 → ‖X‖ < r → ∑' n, d n * X ^ n = 0 := by
    intro X hX hXr
    have hsb : Summable fun n => b n * X ^ n := by
      refine Summable.of_norm_bounded hsumm fun n => ?_
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hXr.le n) (norm_nonneg _)
    have hsc : Summable fun n => (if n = k then c else 0 : ℂ) * X ^ n := by
      apply summable_of_ne_finset_zero (s := {k})
      intro n hn
      simp only [Finset.mem_singleton] at hn
      simp [hn]
    have hsplit : (fun n => d n * X ^ n) =
        fun n => b n * X ^ n - (if n = k then c else 0 : ℂ) * X ^ n := by
      funext n; simp [hd, sub_mul]
    rw [hsplit, hsb.tsum_sub hsc, hval X hX hXr]
    rw [tsum_eq_single k (fun n hn => by simp [hn])]
    simp
  have h := coeff_eq_zero_of_tsum_eq_zero hr hsumm' hzero
  intro n
  have := h n
  simp only [hd, sub_eq_zero] at this
  exact this

end Langlands.RankinSelberg.HighlyRamified
