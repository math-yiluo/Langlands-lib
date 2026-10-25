import Langlands.Representation.RankinSelberg.HolomorphicRationalContinuationStatement
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Regularity of holomorphic rational continuations

Analytic uniqueness extends the cross-multiplied continuation identity to the
positive half-plane. Coprimality excludes denominator zeros, and pointwise
complex logarithms transfer the conclusion to the punctured unit disk.
-/

namespace Langlands.RankinSelberg

open Filter Set
open scoped Topology

private theorem differentiable_spectralPoint {q : ℕ} (hq : 1 < q) :
    Differentiable ℂ (spectralPoint q) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_trans Nat.zero_lt_one hq))
  exact differentiable_id.neg.const_cpow (Or.inl hq0)

private theorem exists_spectralPoint_of_norm_lt_one {q : ℕ} (hq : 1 < q)
    {z : ℂ} (hz : 0 < ‖z‖) (hz1 : ‖z‖ < 1) :
    ∃ s : ℂ, 0 < s.re ∧ spectralPoint q s = z := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos hqR
  have hlogC : (Real.log (q : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hlog)
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_trans Nat.zero_lt_one hq))
  refine ⟨-Complex.log z / (Real.log (q : ℝ) : ℂ), ?_, ?_⟩
  · rw [Complex.div_ofReal_re, Complex.neg_re, Complex.log_re]
    exact div_pos (neg_pos.mpr (Real.log_neg hz hz1)) hlog
  · rw [spectralPoint, Complex.cpow_def_of_ne_zero hqC, ← Complex.natCast_log]
    have he : (Real.log (q : ℝ) : ℂ) *
        -(-Complex.log z / (Real.log (q : ℝ) : ℂ)) = Complex.log z := by
      field_simp
    rw [he, Complex.exp_log (norm_pos_iff.mp hz)]

/-- Holomorphy on the positive half-plane forces the reduced rational
continuation to be regular throughout the punctured unit disk. -/
theorem holomorphicRationalContinuation : HolomorphicRationalContinuationStatement := by
  intro q hq f R hf hR
  let H : Set ℂ := {s : ℂ | 0 < s.re}
  have hH : IsOpen H := isOpen_lt continuous_const Complex.continuous_re
  have hHconn : IsPreconnected H := (convex_halfSpace_re_gt 0).isPreconnected
  have hD : Differentiable ℂ (fun s => R.denom.eval (spectralPoint q s)) :=
    R.denom.differentiable.comp (differentiable_spectralPoint hq)
  have hN : Differentiable ℂ (fun s => R.num.eval (spectralPoint q s)) :=
    R.num.differentiable.comp (differentiable_spectralPoint hq)
  obtain ⟨a, ha⟩ := hR
  let t : ℂ := ((max a 0 + 1 : ℝ) : ℂ)
  have htH : t ∈ H := by
    change 0 < max a 0 + 1
    linarith [le_max_right a 0]
  have hta : a < t.re := by
    change a < max a 0 + 1
    linarith [le_max_left a 0]
  have hlocal : (fun s => f s * R.denom.eval (spectralPoint q s)) =ᶠ[𝓝 t]
      (fun s => R.num.eval (spectralPoint q s)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hta]
      with s hs
    obtain ⟨hd, he⟩ := ha s hs
    have he' : f s = R.num.eval (spectralPoint q s) /
        R.denom.eval (spectralPoint q s) := by
      simpa only [RatFunc.eval, Polynomial.eval₂_id] using he
    exact (eq_div_iff hd).mp he'
  have hcross : EqOn (fun s => f s * R.denom.eval (spectralPoint q s))
      (fun s => R.num.eval (spectralPoint q s)) H :=
    ((hf.mul hD.differentiableOn).analyticOnNhd hH).eqOn_of_preconnected_of_eventuallyEq
      (hN.differentiableOn.analyticOnNhd hH) hHconn htH hlocal
  have hregular : ∀ s : ℂ, 0 < s.re → R.denom.eval (spectralPoint q s) ≠ 0 := by
    intro s hs hd
    have hn : R.num.eval (spectralPoint q s) = 0 := by
      simpa only [hd, mul_zero] using (hcross hs).symm
    obtain ⟨A, B, hab⟩ := R.isCoprime_num_denom
    have he := congrArg (Polynomial.eval (spectralPoint q s)) hab
    simp [Polynomial.eval_add, Polynomial.eval_mul, hn, hd] at he
  refine ⟨hregular, ?_⟩
  intro z hz hz1
  obtain ⟨s, hs, rfl⟩ := exists_spectralPoint_of_norm_lt_one hq hz hz1
  exact hregular s hs

end Langlands.RankinSelberg
