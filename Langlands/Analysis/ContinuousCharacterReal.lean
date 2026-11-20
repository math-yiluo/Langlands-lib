import Mathlib

/-!
# Continuous characters of the real line

A continuous function `φ : ℝ → ℂ` with `φ 0 = 1` and `φ (u + v) = φ u * φ v` is an exponential
`u ↦ exp (c u)`.

The proof is the classical smoothing argument: `φ u · ∫₀^ε φ = ∫_u^(u+ε) φ`, and `∫₀^ε φ ≠ 0`
for small `ε`, so `φ` is differentiable with `φ' = c φ`.
-/

noncomputable section
set_option autoImplicit false

open intervalIntegral MeasureTheory

namespace Langlands.ContinuousCharacterReal

/-- **Continuous homomorphisms `(ℝ, +) → (ℂ, ×)` are exponentials.** -/
theorem exists_eq_exp {φ : ℝ → ℂ} (hc : Continuous φ) (h0 : φ 0 = 1)
    (hadd : ∀ u v, φ (u + v) = φ u * φ v) : ∃ c : ℂ, ∀ u, φ u = Complex.exp (c * u) := by
  -- a small interval on which `φ` stays near `1`
  have hcont : ContinuousAt φ 0 := hc.continuousAt
  have hev : ∀ᶠ v in nhds (0 : ℝ), ‖φ v - 1‖ < 1 / 2 := by
    have h : ContinuousAt (fun v => ‖φ v - (1 : ℂ)‖) 0 := (hcont.sub continuousAt_const).norm
    have h' := h.tendsto
    simp only [h0, sub_self, norm_zero] at h'
    exact h'.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨ε, hε, hεφ⟩ := Metric.eventually_nhds_iff.mp hev
  set e : ℝ := ε / 2 with he
  have he0 : 0 < e := by rw [he]; linarith
  have hnear : ∀ v ∈ Set.uIoc 0 e, ‖φ v - 1‖ ≤ 1 / 2 := by
    intro v hv
    rw [Set.uIoc_of_le he0.le] at hv
    refine (hεφ ?_).le
    rw [Real.dist_eq, sub_zero, abs_of_pos hv.1]
    linarith [hv.2]
  set A : ℂ := ∫ v in (0 : ℝ)..e, φ v with hAdef
  have hA : A ≠ 0 := by
    have hint : ∫ v in (0 : ℝ)..e, (φ v - 1) = A - (e : ℂ) := by
      rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _)
        intervalIntegrable_const, intervalIntegral.integral_const]
      simp [hAdef]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const hnear
    rw [hint, sub_zero, abs_of_pos he0] at hb
    intro hA0
    rw [hA0, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he0] at hb
    linarith
  -- `φ u * A = ∫_u^(u+e) φ`
  have hshift : ∀ u, φ u * A = ∫ w in u..(u + e), φ w := by
    intro u
    rw [hAdef, ← intervalIntegral.integral_const_mul]
    have hf : (fun v => φ u * φ v) = fun v => φ (u + v) := funext fun v => (hadd u v).symm
    rw [hf, intervalIntegral.integral_comp_add_left (fun w => φ w) u, add_zero]
  -- the derivative
  set c : ℂ := (φ e - 1) / A with hcdef
  have hderiv : ∀ u, HasDerivAt φ (c * φ u) u := by
    intro u
    have h1 := (hc.integral_hasStrictDerivAt 0 (u + e)).hasDerivAt
    have h1' : HasDerivAt (fun x => ∫ w in (0 : ℝ)..(x + e), φ w) (φ (u + e)) u := by
      have := HasDerivAt.scomp (h := fun x : ℝ => x + e) u h1 ((hasDerivAt_id' u).add_const e)
      simp only [one_smul] at this
      exact this
    have h2 := (hc.integral_hasStrictDerivAt 0 u).hasDerivAt
    have h3 : HasDerivAt (fun x => (∫ w in (0 : ℝ)..(x + e), φ w) - ∫ w in (0 : ℝ)..x, φ w)
        (φ (u + e) - φ u) u := h1'.sub h2
    have h4 : (fun x => (∫ w in (0 : ℝ)..(x + e), φ w) - ∫ w in (0 : ℝ)..x, φ w) =
        fun x => φ x * A := by
      funext x
      rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _), hshift x]
    rw [h4] at h3
    have h5 := h3.div_const A
    have h6 : (fun x => φ x * A / A) = φ := funext fun x => mul_div_cancel_right₀ _ hA
    rw [h6] at h5
    convert h5 using 1
    rw [hadd u e, hcdef]
    field_simp
  refine ⟨c, fun u => ?_⟩
  -- `φ u * exp (-c u)` is constant
  let ψ : ℝ → ℂ := fun x => φ x * Complex.exp (-(c * x))
  have hψ : ∀ x, HasDerivAt ψ 0 x := by
    intro x
    have hexp : HasDerivAt (fun y : ℝ => Complex.exp (-(c * y))) (Complex.exp (-(c * x)) * -c) x := by
      have hlin : HasDerivAt (fun y : ℝ => -(c * (y : ℂ))) (-c) x := by
        have h := ((hasDerivAt_id' x).ofReal_comp).const_mul (-c)
        convert h using 1
        · funext y
          simp
        · simp
      exact hlin.cexp
    have h := (hderiv x).mul hexp
    convert h using 1
    ring
  have hconst := is_const_of_deriv_eq_zero (fun x => (hψ x).differentiableAt)
    (fun x => (hψ x).deriv) u 0
  have hψ0 : ψ 0 = 1 := by simp [ψ, h0]
  have hu : φ u * Complex.exp (-(c * u)) = 1 := by
    change ψ u = 1
    rw [hconst, hψ0]
  have hexpne := Complex.exp_ne_zero (-(c * u))
  calc φ u = φ u * Complex.exp (-(c * u)) * Complex.exp (c * u) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = Complex.exp (c * u) := by rw [hu, one_mul]

end Langlands.ContinuousCharacterReal
