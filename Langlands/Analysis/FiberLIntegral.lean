import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.Normed.Lp.lpSpace

/-! # Integrals of functions constant on the fibers of a map, and `ℓ²` norms

* `lintegral_comp_eq_mul_tsum`: if every fiber of `p : Q → ι` is measurable of measure
  `c ≠ 0`, then `∫⁻ q, v (p q) ∂μ = c * ∑' i, v i` for every `v : ι → ℝ≥0∞`. No
  measurability or countability of `v` is assumed.
* `lp_two_enorm_sq_eq_tsum` and `memℓp_two_of_tsum_enorm_ne_top`: the squared norm of an
  element of `ℓ²(X, ℂ)` as an extended nonnegative sum, and membership in `ℓ²` from finiteness
  of that sum.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace Langlands.Analysis

/-- Let `p : Q → ι` have measurable fibers, all of measure `c ≠ 0`. Then a function of
the form `v ∘ p` has integral `c * ∑' i, v i`. -/
theorem lintegral_comp_eq_mul_tsum {Q ι : Type*} [MeasurableSpace Q] (μ : Measure Q)
    (p : Q → ι) (c : ℝ≥0∞) (hc : c ≠ 0)
    (hmeas : ∀ i, MeasurableSet (p ⁻¹' {i})) (hμ : ∀ i, μ (p ⁻¹' {i}) = c)
    (v : ι → ℝ≥0∞) :
    ∫⁻ q, v (p q) ∂μ = c * ∑' i, v i := by
  classical
  have hind : ∀ (i : ι) (q : Q),
      (p ⁻¹' {i}).indicator (fun _ => v i) q = if p q = i then v i else 0 := by
    intro i q
    simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff]
  have hint : ∀ i, ∫⁻ q, (p ⁻¹' {i}).indicator (fun _ => v i) q ∂μ = v i * c := by
    intro i
    rw [lintegral_indicator_const (hmeas i), hμ]
  apply le_antisymm
  · by_cases htop : ∑' i, v i = ∞
    · rw [htop, ENNReal.mul_top hc]
      exact le_top
    have hS : (Function.support v).Countable := Summable.countable_support_ennreal htop
    have : Countable (Function.support v) := hS.to_subtype
    have hle : ∀ q, v (p q) ≤
        ∑' i : Function.support v, (p ⁻¹' {(i : ι)}).indicator (fun _ => v i) q := by
      intro q
      by_cases hq : v (p q) = 0
      · rw [hq]
        exact zero_le
      · refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (⟨p q, hq⟩ : Function.support v))
        rw [hind]
        simp
    calc ∫⁻ q, v (p q) ∂μ
        ≤ ∫⁻ q, ∑' i : Function.support v,
            (p ⁻¹' {(i : ι)}).indicator (fun _ => v i) q ∂μ := lintegral_mono hle
      _ = ∑' i : Function.support v,
            ∫⁻ q, (p ⁻¹' {(i : ι)}).indicator (fun _ => v i) q ∂μ :=
          lintegral_tsum fun i => aemeasurable_const.indicator (hmeas i)
      _ = ∑' i : Function.support v, v i * c := by
          congr 1
          ext i
          exact hint i
      _ = c * ∑' i : Function.support v, v i := by
          rw [ENNReal.tsum_mul_right, mul_comm]
      _ ≤ c * ∑' i, v i := by
          gcongr
          exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective v
  · rw [← ENNReal.tsum_mul_left, ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    calc ∑ i ∈ s, c * v i
        = ∑ i ∈ s, ∫⁻ q, (p ⁻¹' {i}).indicator (fun _ => v i) q ∂μ := by
          congr 1
          ext i
          rw [hint, mul_comm]
      _ = ∫⁻ q, ∑ i ∈ s, (p ⁻¹' {i}).indicator (fun _ => v i) q ∂μ :=
          (lintegral_finsetSum s fun i _ => measurable_const.indicator (hmeas i)).symm
      _ ≤ ∫⁻ q, v (p q) ∂μ := by
          apply lintegral_mono
          intro q
          simp only [hind]
          rw [Finset.sum_ite_eq]
          split_ifs
          · exact le_rfl
          · exact zero_le

/-- The squared norm of an element of `ℓ²(X, ℂ)` as an extended nonnegative sum. -/
theorem lp_two_enorm_sq_eq_tsum {X : Type*} (F : lp (fun _ : X => ℂ) 2) :
    ‖F‖ₑ ^ 2 = ∑' α, ‖F α‖ₑ ^ 2 := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have h1 := lp.norm_rpow_eq_tsum hp F
  have hs : Summable fun α => ‖F α‖ ^ (2 : ℝ≥0∞).toReal := (lp.memℓp F).summable hp
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h1 hs
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), h1,
    ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hs]
  congr 1
  ext α
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- A function `X → ℂ` with finite extended sum of squared norms lies in `ℓ²`. -/
theorem memℓp_two_of_tsum_enorm_ne_top {X : Type*} (f : X → ℂ)
    (h : ∑' α, ‖f α‖ₑ ^ 2 ≠ ∞) : Memℓp f 2 := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  rw [memℓp_gen_iff hp]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  have h' : Summable fun α => (‖f α‖₊ ^ 2 : ℝ≥0) := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable]
    simpa [enorm, ENNReal.coe_pow] using h
  exact (NNReal.summable_coe.mpr h').congr fun α => by simp

end Langlands.Analysis
