import Langlands.Representation.RankinSelberg.HolomorphicRationalContinuationProof
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Regularity of rational continuations on the boundary line `Re(s) = 1`

`holomorphicRationalContinuation` makes a rational continuation regular wherever the
continued function is holomorphic on an open half-plane. Unitary JPSS integrals are only
known to converge on the closed half-plane `Re(s) ≥ 1`. This module adds the boundary:

* `norm_integral_cpow_le_of_strip`: a Mellin-type integral `∫ c · d^(s-κ)` that converges at
  `s = 1` and `s = 2` is bounded on the closed strip `1 ≤ Re(s) ≤ 2`;
* `denom_ne_zero_of_bounded_continuation`: if `f` is holomorphic on `Re(s) > 1`, bounded on
  `1 < Re(s) < 2` and has the rational continuation `R` in `q^(-s)`, then the denominator of
  `R` does not vanish at `q^(-s)` for any `s` with `Re(s) ≥ 1`. On `Re(s) > 1` this is the
  argument of `holomorphicRationalContinuation`. At a point of the line `Re(s) = 1`, a zero of
  the denominator is not a zero of the coprime numerator, so `R(q^(-s))` would be unbounded
  near it, against the boundedness of `f`.
-/

noncomputable section

namespace Langlands.RankinSelberg.UnitaryGeneric

open Filter Set MeasureTheory
open scoped Topology

theorem differentiable_spectralPoint' {q : ℕ} (hq : 1 < q) :
    Differentiable ℂ (spectralPoint q) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_trans Nat.zero_lt_one hq))
  exact differentiable_id.neg.const_cpow (Or.inl hq0)

/-- A power `d^σ` with `1 ≤ σ ≤ 2` is at most `d^1 + d^2`. -/
theorem rpow_le_add_of_mem_Icc {d σ κ : ℝ} (hd : 0 < d) (h1 : 1 ≤ σ) (h2 : σ ≤ 2) :
    d ^ (σ - κ) ≤ d ^ (1 - κ) + d ^ (2 - κ) := by
  rcases le_total 1 d with hd1 | hd1
  · exact (Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hd.le _))
  · exact (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hd.le _))

/-- A Mellin-type integral converging at `s = 1` and `s = 2` is bounded on the strip. -/
theorem norm_integral_cpow_le_of_strip {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (c : X → ℂ) (d : X → ℝ) (hd : ∀ x, 0 < d x) (κ : ℝ)
    (h1 : Integrable (fun x => c x * (d x : ℂ) ^ ((1 : ℂ) - κ)) μ)
    (h2 : Integrable (fun x => c x * (d x : ℂ) ^ ((2 : ℂ) - κ)) μ)
    (s : ℂ) (hs1 : 1 ≤ s.re) (hs2 : s.re ≤ 2) :
    ‖∫ x, c x * (d x : ℂ) ^ (s - κ) ∂μ‖ ≤
      ∫ x, (‖c x * (d x : ℂ) ^ ((1 : ℂ) - κ)‖ + ‖c x * (d x : ℂ) ^ ((2 : ℂ) - κ)‖) ∂μ := by
  refine norm_integral_le_of_norm_le (h1.norm.add h2.norm) (Eventually.of_forall fun x => ?_)
  simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hd x), Complex.sub_re,
    Complex.ofReal_re, Complex.one_re, Complex.re_ofNat]
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (rpow_le_add_of_mem_Icc (hd x) hs1 hs2) (norm_nonneg _)

/-- **Boundary regularity.** Let `f` be holomorphic on `Re(s) > 1`, bounded on
`1 < Re(s) < 2`, with rational continuation `R` in `q^(-s)`. Then the denominator of `R` does
not vanish at `q^(-s)` for every `s` with `Re(s) ≥ 1`. -/
theorem denom_ne_zero_of_bounded_continuation {q : ℕ} (hq : 1 < q) (f : ℂ → ℂ)
    (R : RatFunc ℂ) (hf : DifferentiableOn ℂ f {s : ℂ | 1 < s.re})
    (hR : HasRationalContinuation q f R) (B : ℝ)
    (hB : ∀ s : ℂ, 1 < s.re → s.re < 2 → ‖f s‖ ≤ B) :
    ∀ s : ℂ, 1 ≤ s.re → R.denom.eval (spectralPoint q s) ≠ 0 := by
  let H : Set ℂ := {s : ℂ | 1 < s.re}
  have hH : IsOpen H := isOpen_lt continuous_const Complex.continuous_re
  have hHconn : IsPreconnected H := (convex_halfSpace_re_gt 1).isPreconnected
  have hD : Differentiable ℂ (fun s => R.denom.eval (spectralPoint q s)) :=
    R.denom.differentiable.comp (differentiable_spectralPoint' hq)
  have hN : Differentiable ℂ (fun s => R.num.eval (spectralPoint q s)) :=
    R.num.differentiable.comp (differentiable_spectralPoint' hq)
  obtain ⟨a, ha⟩ := hR
  let t : ℂ := ((max a 1 + 1 : ℝ) : ℂ)
  have htH : t ∈ H := by
    change 1 < max a 1 + 1
    linarith [le_max_right a 1]
  have hta : a < t.re := by
    change a < max a 1 + 1
    linarith [le_max_left a 1]
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
  -- coprimality: the numerator and denominator have no common zero
  have hcop : ∀ s : ℂ, R.denom.eval (spectralPoint q s) = 0 →
      R.num.eval (spectralPoint q s) ≠ 0 := by
    intro s hd hn
    obtain ⟨A, B', hab⟩ := R.isCoprime_num_denom
    have he := congrArg (Polynomial.eval (spectralPoint q s)) hab
    simp [Polynomial.eval_add, Polynomial.eval_mul, hn, hd] at he
  intro s0 hs0 hd0
  have hn0 := hcop s0 hd0
  rcases lt_or_eq_of_le hs0 with hlt | heq
  · -- inside the open half-plane
    have := hcross hlt
    simp only at this
    rw [hd0, mul_zero] at this
    exact hn0 this.symm
  · -- on the boundary line: approach `s0` from the right
    let g : ℝ → ℂ := fun ε => s0 + (ε : ℂ)
    have hg : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 s0) := by
      have hc : Continuous g := continuous_const.add Complex.continuous_ofReal
      have := hc.tendsto 0
      simp only [g, Complex.ofReal_zero, add_zero] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    have hNlim : Tendsto (fun ε => ‖R.num.eval (spectralPoint q (g ε))‖) (𝓝[>] (0 : ℝ))
        (𝓝 ‖R.num.eval (spectralPoint q s0)‖) :=
      ((hN.continuous.tendsto s0).comp hg).norm
    have hDlim : Tendsto (fun ε => B * ‖R.denom.eval (spectralPoint q (g ε))‖)
        (𝓝[>] (0 : ℝ)) (𝓝 (B * ‖R.denom.eval (spectralPoint q s0)‖)) :=
      (((hD.continuous.tendsto s0).comp hg).norm).const_mul B
    have hev : (fun ε => ‖R.num.eval (spectralPoint q (g ε))‖) ≤ᶠ[𝓝[>] (0 : ℝ)]
        (fun ε => B * ‖R.denom.eval (spectralPoint q (g ε))‖) := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
      have hre : (g ε).re = 1 + ε := by
        simp only [g, Complex.add_re, Complex.ofReal_re, ← heq]
      have h1 : 1 < (g ε).re := by rw [hre]; linarith [hε.1]
      have h2 : (g ε).re < 2 := by rw [hre]; linarith [hε.2]
      have hc := hcross h1
      simp only at hc
      rw [← hc, norm_mul]
      exact mul_le_mul_of_nonneg_right (hB _ h1 h2) (norm_nonneg _)
    have hle := le_of_tendsto_of_tendsto hNlim hDlim hev
    rw [hd0, norm_zero, mul_zero] at hle
    exact hn0 (norm_le_zero_iff.mp hle)

end Langlands.RankinSelberg.UnitaryGeneric
