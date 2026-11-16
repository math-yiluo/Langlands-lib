import Langlands.Representation.Archimedean.ComplexGLTwoWirtinger
import Langlands.Representation.Archimedean.ComplexSwapJacquetNonvanishing

/-!
# The radial integrals `∫_ℂ (1 + |z|²)^β |z|^(2k) dz`

For `Re β + k < -1` the function `(1 + |z|²)^β (z z̄)^k` is integrable on `ℂ`
(`integrable_rad`). Writing `I(β, k)` for its integral, `|z|² = (1 + |z|²) - 1` gives
`I(β, k + 1) = I(β + 1, k) - I(β, k)` (`radInt_succ`), and `I(β, 0) = π / (-(β + 1))`
(`ComplexSwapJacquet.integral_one_add_norm_sq_cpow`). By induction on `k`,
`I(β, k) ∏_{j=1}^{k+1} (-(β + j)) = π k!` (`radInt_mul_prod`); in particular `I(β, k) ≠ 0`
(`radInt_ne_zero`).
-/

noncomputable section

open Complex ComplexConjugate Filter MeasureTheory

namespace Langlands.Archimedean.ComplexGLTwoNoncompact

/-- `(1 + |z|²)^β (z z̄)^k`. -/
def rad (β : ℂ) (k : ℕ) (z : ℂ) : ℂ := pw β z * (z * conj z) ^ k

/-- `I(β, k) = ∫_ℂ (1 + |z|²)^β (z z̄)^k dz`. -/
def radInt (β : ℂ) (k : ℕ) : ℂ := ∫ z : ℂ, rad β k z

theorem norm_pw (σ z : ℂ) : ‖pw σ z‖ = (1 + ‖z‖ ^ 2) ^ σ.re := by
  rw [pw, Complex.norm_exp, Complex.re_mul_ofReal, Real.rpow_def_of_pos (one_add_norm_sq_pos z)]
  ring_nf

theorem pw_natCast (k : ℕ) (z : ℂ) : pw (k : ℂ) z = W z ^ k := by
  induction k with
  | zero => simp [pw_zero]
  | succ k ih => rw [Nat.cast_succ, pw_add_one, ih, pow_succ]

theorem continuous_pw' (σ : ℂ) : Continuous (pw σ) := by
  have hL : Continuous fun z : ℂ => Real.log (1 + ‖z‖ ^ 2) :=
    (continuous_const.add (continuous_norm.pow 2)).log fun z => (one_add_norm_sq_pos z).ne'
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hL))

theorem continuous_rad (β : ℂ) (k : ℕ) : Continuous (rad β k) :=
  (continuous_pw' β).mul ((continuous_id.mul Complex.continuous_conj).pow k)

theorem integrable_pw {σ : ℂ} (hσ : σ.re < -1) : Integrable (pw σ) := by
  have hr : ((Module.finrank ℝ ℂ : ℕ) : ℝ) < -2 * σ.re := by
    rw [Complex.finrank_real_complex]
    push_cast
    linarith
  refine (integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure ℂ)) hr).mono'
    (continuous_pw' σ).aestronglyMeasurable (Eventually.of_forall fun z => le_of_eq ?_)
  rw [norm_pw]
  congr 1
  ring

theorem norm_rad_le (β : ℂ) (k : ℕ) (z : ℂ) : ‖rad β k z‖ ≤ ‖pw (β + k) z‖ := by
  rw [rad, pw_add, pw_natCast, norm_mul, norm_mul, norm_pow, norm_pow]
  gcongr
  rw [Complex.mul_conj, Complex.norm_real, W_eq, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, Complex.normSq_eq_norm_sq, abs_of_nonneg (sq_nonneg _),
    abs_of_pos (one_add_norm_sq_pos z)]
  linarith

theorem integrable_rad {β : ℂ} {k : ℕ} (hβ : β.re + k < -1) : Integrable (rad β k) := by
  have hσ : (β + k).re < -1 := by
    simpa using hβ
  exact (integrable_pw hσ).norm.mono' (continuous_rad β k).aestronglyMeasurable
    (Eventually.of_forall (norm_rad_le β k))

theorem rad_succ (β : ℂ) (k : ℕ) (z : ℂ) : rad β (k + 1) z = rad (β + 1) k z - rad β k z := by
  rw [rad, rad, rad, pw_add_one, W]
  ring

theorem radInt_succ {β : ℂ} {k : ℕ} (hβ : β.re + (k + 1 : ℕ) < -1) :
    radInt β (k + 1) = radInt (β + 1) k - radInt β k := by
  have h1 : (β + 1).re + k < -1 := by
    push_cast at hβ
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have h2 : β.re + k < -1 := by
    push_cast at hβ
    linarith
  rw [radInt, radInt, radInt, ← integral_sub (integrable_rad h1) (integrable_rad h2)]
  congr 1
  funext z
  exact rad_succ β k z

theorem radInt_zero {β : ℂ} (hβ : β.re < -1) : radInt β 0 = (Real.pi : ℂ) / (-(β + 1)) := by
  rw [radInt, ← ComplexSwapJacquet.integral_one_add_norm_sq_cpow hβ]
  congr 1
  funext z
  rw [rad, pow_zero, mul_one, pw]

/-- `I(β, k) ∏_{j=1}^{k+1} (-(β + j)) = π k!`. -/
theorem radInt_mul_prod (k : ℕ) {β : ℂ} (hβ : β.re + k < -1) :
    radInt β k * ∏ j ∈ Finset.range (k + 1), (-(β + ((j : ℂ) + 1))) =
      (Real.pi : ℂ) * (k.factorial : ℂ) := by
  induction k generalizing β with
  | zero =>
    have hβ' : β.re < -1 := by simpa using hβ
    have hβ1 : β + 1 ≠ 0 := by
      intro h
      have h' := congrArg Complex.re h
      simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at h'
      linarith
    rw [radInt_zero hβ', Finset.prod_range_one, Nat.factorial_zero]
    push_cast
    field_simp
    ring
  | succ k ih =>
    have h1 : (β + 1).re + k < -1 := by
      push_cast at hβ
      simp only [Complex.add_re, Complex.one_re]
      linarith
    have h2 : β.re + k < -1 := by
      push_cast at hβ
      linarith
    have ih1 := ih h1
    have ih2 := ih h2
    rw [radInt_succ hβ]
    have hp1 : ∏ j ∈ Finset.range (k + 1 + 1), (-(β + ((j : ℂ) + 1))) =
        (∏ j ∈ Finset.range (k + 1), (-(β + ((j : ℂ) + 1)))) * (-(β + ((k : ℂ) + 2))) := by
      rw [Finset.prod_range_succ]
      push_cast
      ring
    have hp2 : ∏ j ∈ Finset.range (k + 1 + 1), (-(β + ((j : ℂ) + 1))) =
        (∏ j ∈ Finset.range (k + 1), (-(β + 1 + ((j : ℂ) + 1)))) * (-(β + 1)) := by
      rw [Finset.prod_range_succ']
      congr 1
      · apply Finset.prod_congr rfl
        intro j _
        push_cast
        ring
      · push_cast
        ring
    have e : (radInt (β + 1) k - radInt β k) *
        ∏ j ∈ Finset.range (k + 1 + 1), (-(β + ((j : ℂ) + 1))) =
        radInt (β + 1) k * ((∏ j ∈ Finset.range (k + 1), (-(β + 1 + ((j : ℂ) + 1)))) *
            (-(β + 1))) -
          radInt β k * ((∏ j ∈ Finset.range (k + 1), (-(β + ((j : ℂ) + 1)))) *
            (-(β + ((k : ℂ) + 2)))) := by
      rw [sub_mul]
      congr 1
      · rw [hp2]
      · rw [hp1]
    rw [e, Nat.factorial_succ]
    push_cast
    linear_combination (-(β + 1)) * ih1 - (-(β + ((k : ℂ) + 2))) * ih2

theorem radInt_ne_zero {β : ℂ} {k : ℕ} (hβ : β.re + k < -1) : radInt β k ≠ 0 := by
  intro h
  have h' := radInt_mul_prod k hβ
  rw [h, zero_mul] at h'
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  exact mul_ne_zero hpi hf h'.symm

end Langlands.Archimedean.ComplexGLTwoNoncompact
