import Langlands.Global.RankinSelberg.RealLowestWeightFourier
import Langlands.Representation.Archimedean.RealBlockFlatJacquet
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! # Fourier estimates for real discrete-series angular modes -/

noncomputable section

open Complex MeasureTheory
open scoped FourierTransform

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealDiscreteReciprocalFourier

open RealLowestWeightFourier
open Langlands.Archimedean.RealBlockFourierFinite
open Langlands.Archimedean.RealBlockFlatJacquet (expMode_one_eq)

/-- The rational cell profile of a single angular mode, with `m` extra pairs of powers. -/
def modeKernel (k m : ℕ) (x : ℝ) : ℂ :=
  (1 + (x : ℂ) * I) ^ m * (1 - (x : ℂ) * I)⁻¹ ^ (k + 1 + m)

private theorem norm_positiveExpPower_le (k : ℕ) (hk : k ≠ 0)
    (η : ℝ) (hη : 0 ≤ η) (hηk : η ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, ‖positiveExpPower 1 k y‖ ≤ C * |y| ^ η := by
  let A : ℝ := (2 * Real.pi) ^ (k + 1) / k.factorial
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let C := max A (2 * Real.pi)
  have hC : 0 ≤ C := hA.trans (le_max_left _ _)
  refine ⟨C, hC, fun y => ?_⟩
  have hnorm : ‖positiveExpPower 1 k y‖ = A * (max y 0) ^ k * Real.exp (-(2 * Real.pi * y)) := by
    simp only [positiveExpPower, mul_one, norm_mul, norm_div, norm_pow, Complex.norm_exp,
      Complex.neg_re, Complex.ofReal_re, Complex.norm_real,
      Real.norm_of_nonneg (le_max_right _ _), Complex.norm_ofNat,
      Complex.norm_of_nonneg (show 0 ≤ Real.pi from Real.pi_pos.le), Complex.norm_natCast]
    rfl
  rw [hnorm]
  by_cases hy : y ≤ 0
  · rw [max_eq_right hy, zero_pow hk, mul_zero, zero_mul]
    exact mul_nonneg hC (Real.rpow_nonneg (abs_nonneg _) _)
  have hy₀ : 0 ≤ y := le_of_not_ge hy
  rw [max_eq_left (le_of_not_ge hy), abs_of_pos (lt_of_not_ge hy)]
  rcases le_or_gt y 1 with hy₁ | hy₁
  · have hpow : y ^ k ≤ y ^ η := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge (lt_of_not_ge hy) hy₁ hηk
    have hexp : Real.exp (-(2 * Real.pi * y)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (by positivity) (le_of_not_ge hy)))
    calc
      _ ≤ A * y ^ k := mul_le_of_le_one_right (mul_nonneg hA (pow_nonneg hy₀ _)) hexp
      _ ≤ C * y ^ η := mul_le_mul (le_max_left _ _) hpow (pow_nonneg hy₀ _) hC
  · have hb := Real.pow_div_factorial_le_exp (x := 2 * Real.pi * y)
      (mul_nonneg (by positivity) (le_of_not_ge hy)) k
    have hfac : A * y ^ k = 2 * Real.pi * ((2 * Real.pi * y) ^ k / k.factorial) := by
      dsimp [A]
      rw [pow_succ', mul_pow]
      ring
    have hpow : 1 ≤ y ^ η := Real.one_le_rpow hy₁.le hη
    calc
      _ = 2 * Real.pi * ((2 * Real.pi * y) ^ k / k.factorial) *
          Real.exp (-(2 * Real.pi * y)) := by rw [hfac]
      _ ≤ 2 * Real.pi * Real.exp (2 * Real.pi * y) * Real.exp (-(2 * Real.pi * y)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by positivity)) (Real.exp_pos _).le
      _ = 2 * Real.pi := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      _ ≤ C * y ^ η := (le_max_right _ _).trans (le_mul_of_one_le_right hC hpow)

private theorem modeKernel_succ (k m : ℕ) :
    modeKernel k (m + 1) = fun x => 2 * modeKernel (k + 1) m x - modeKernel k m x := by
  funext x
  let a : ℂ := 1 + (x : ℂ) * I
  let b : ℂ := 1 - (x : ℂ) * I
  have h : a = 2 - b := by dsimp [a, b]; ring
  have hb : b ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp [b, Complex.mul_re] at hh
  change a ^ (m + 1) * b⁻¹ ^ (k + 1 + (m + 1)) =
    2 * (a ^ m * b⁻¹ ^ (k + 1 + 1 + m)) - a ^ m * b⁻¹ ^ (k + 1 + m)
  rw [show k + 1 + (m + 1) = k + 1 + 1 + m by omega,
    show k + 1 + 1 + m = (k + 1 + m) + 1 by omega, pow_succ a, pow_succ b⁻¹]
  calc
    _ = a ^ m * b⁻¹ ^ (k + 1 + m) * (a * b⁻¹) := by ring
    _ = _ := by
      rw [h, sub_mul, mul_inv_cancel₀ hb]
      ring

private theorem fourier_sub_double {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (t : ℝ) :
    𝓕 (fun x => 2 * f x - g x) t = 2 * 𝓕 f t - 𝓕 g t := by
  let phase (x : ℝ) := exp (↑(-2 * Real.pi * x * t) * I)
  have hf' : Integrable (fun x => phase x * f x) := by
    apply (Real.fourierIntegral_convergent_iff (E := ℂ) (μ := volume) t).2 at hf
    simpa only [phase, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, Real.inner_apply,
      mul_neg, neg_mul, mul_assoc] using hf
  have hg' : Integrable (fun x => phase x * g x) := by
    apply (Real.fourierIntegral_convergent_iff (E := ℂ) (μ := volume) t).2 at hg
    simpa only [phase, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, Real.inner_apply,
      mul_neg, neg_mul, mul_assoc] using hg
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  change (∫ x, phase x * (2 * f x - g x)) = _
  have h (x : ℝ) : phase x * (2 * f x - g x) = 2 * (phase x * f x) - phase x * g x := by ring
  simp_rw [h]
  rw [integral_sub (hf'.const_mul 2) hg', integral_const_mul]

/-- The rational mode is integrable, and its Fourier transform satisfies a global
power bound with any exponent between zero and `k`. -/
theorem modeKernel_fourier_bound (k m : ℕ) (hk : k ≠ 0) {η : ℝ} (hη : 0 ≤ η) (hηk : η ≤ k) :
    Integrable (modeKernel k m) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, ‖𝓕 (modeKernel k m) y‖ ≤ C * |y| ^ η := by
  induction m generalizing k with
  | zero =>
    let f := fun x : ℝ => (1 - (x : ℂ) * I)⁻¹ ^ (k + 1)
    have h : modeKernel k 0 = f := by funext x; simp [modeKernel, f]
    obtain ⟨hf, hF⟩ := realLowestWeightFourier 1 one_pos k hk
    change Integrable (modeKernel k 0) ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y : ℝ, ‖𝓕 (modeKernel k 0) y‖ ≤ C * |y| ^ η
    rw [h, show 𝓕 f = positiveExpPower 1 k by simpa only [Complex.ofReal_one, f] using hF]
    exact ⟨hf, norm_positiveExpPower_le k hk η hη hηk⟩
  | succ m ih =>
    have hηk' : η ≤ (k + 1 : ℕ) := hηk.trans (by exact_mod_cast Nat.le_succ k)
    obtain ⟨hf, A, hA, hAf⟩ := ih (k + 1) (Nat.succ_ne_zero k) hηk'
    obtain ⟨hg, B, hB, hBg⟩ := ih k hk hηk
    rw [modeKernel_succ]
    refine ⟨(hf.const_mul (2 : ℂ)).sub hg, 2 * A + B, by positivity, fun y => ?_⟩
    rw [fourier_sub_double hf hg]
    calc
      _ ≤ ‖2 * 𝓕 (modeKernel (k + 1) m) y‖ + ‖𝓕 (modeKernel k m) y‖ := norm_sub_le _ _
      _ ≤ 2 * (A * |y| ^ η) + B * |y| ^ η := by
        rw [norm_mul, Complex.norm_ofNat]
        exact add_le_add (mul_le_mul_of_nonneg_left (hAf y) (by norm_num)) (hBg y)
      _ = _ := by ring

/-- The angular profile evaluated at the compact factor of the rank-two Jacquet cell. -/
def angularKernel (k : ℕ) (j : ℤ) (x : ℝ) : ℂ :=
  ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)⁻¹ ^ (k + 1) * expMode j (Real.arctan x)

private theorem expMode_nat (n : ℕ) (θ : ℝ) :
    expMode (n : ℤ) θ = expMode 1 θ ^ n := by
  simp only [expMode, Int.cast_natCast, Int.cast_one, one_mul, mul_assoc, exp_nat_mul]

private theorem angularKernel_of_nonnegative (k m : ℕ) (x : ℝ) :
    angularKernel k ((k + 1 + 2 * m : ℕ) : ℤ) x = modeKernel k m x := by
  let ρ := Real.sqrt (1 + x ^ 2)
  let a : ℂ := 1 + (x : ℂ) * I
  let b : ℂ := 1 - (x : ℂ) * I
  have hρ : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
  have hb : b ≠ 0 := by
    intro hh
    have h := congrArg Complex.re hh
    simp [b, Complex.mul_re] at h
  have hρSq : (ρ : ℂ) ^ 2 = 1 + (x : ℂ) ^ 2 := by
    exact_mod_cast Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity)
  have hab : a * b = (ρ : ℂ) ^ 2 := by
    rw [hρSq]
    dsimp [a, b]
    linear_combination -((x : ℂ) ^ 2) * Complex.I_sq
  have hinv : (ρ : ℂ)⁻¹ ^ 2 * a = b⁻¹ := by
    field_simp [hρ, hb]
    linear_combination hab
  have hmode : expMode 1 (Real.arctan x) = a / (ρ : ℂ) := by
    rw [expMode_one_eq, Real.cos_arctan, Real.sin_arctan]
    simp only [Complex.ofReal_div, Complex.ofReal_one, ← show (Real.sqrt (1 + x ^ 2)) = ρ from rfl]
    field_simp [hρ]
    dsimp [a]
    ring
  change (ρ : ℂ)⁻¹ ^ (k + 1) * expMode ((k + 1 + 2 * m : ℕ) : ℤ) (Real.arctan x) =
    a ^ m * b⁻¹ ^ (k + 1 + m)
  rw [expMode_nat, hmode, div_eq_mul_inv, mul_pow]
  calc
    _ = a ^ m * ((ρ : ℂ)⁻¹ ^ 2 * a) ^ (k + 1 + m) := by
      rw [mul_pow, ← pow_mul]
      have he₁ : 2 * (k + 1 + m) = (k + 1) + (k + 1 + 2 * m) := by omega
      have he₂ : m + (k + 1 + m) = k + 1 + 2 * m := by omega
      rw [he₁, pow_add ((ρ : ℂ)⁻¹), show a ^ (k + 1 + 2 * m) = a ^ m * a ^ (k + 1 + m) by
        rw [← pow_add, he₂]]
      ring
    _ = _ := by rw [hinv]

private theorem angularKernel_neg (k : ℕ) (j : ℤ) (x : ℝ) :
    angularKernel k (-j) x = angularKernel k j (-x) := by
  simp only [angularKernel, neg_sq, Real.arctan_neg, expMode, Int.cast_neg, Complex.ofReal_neg,
    neg_mul, mul_neg]

/-- Any angular mode in the high-mode range gives the uniform Fourier power bound
for the associated rational profile. -/
theorem angularKernel_fourier_bound (k m : ℕ) (hk : k ≠ 0) {j : ℤ}
    (hj : j = ((k + 1 + 2 * m : ℕ) : ℤ) ∨ j = -((k + 1 + 2 * m : ℕ) : ℤ))
    {η : ℝ} (hη : 0 ≤ η) (hηk : η ≤ k) :
    Integrable (angularKernel k j) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, ‖𝓕 (angularKernel k j) y‖ ≤ C * |y| ^ η := by
  have he : angularKernel k ((k + 1 + 2 * m : ℕ) : ℤ) = modeKernel k m :=
    funext (angularKernel_of_nonnegative k m)
  rcases hj with rfl | rfl
  · rw [he]
    exact modeKernel_fourier_bound k m hk hη hηk
  · have hneg : angularKernel k (-((k + 1 + 2 * m : ℕ) : ℤ)) =
        fun x => modeKernel k m (-x) := by
      funext x
      rw [angularKernel_neg, he]
    rw [hneg, ← Real.fourierInv_eq_fourier_comp_neg]
    obtain ⟨hi, C, hC, hb⟩ := modeKernel_fourier_bound k m hk hη hηk
    refine ⟨hi.comp_neg, C, hC, fun y => ?_⟩
    simpa only [Real.fourierInv_eq_fourier_neg, abs_neg] using hb (-y)

/-- Each permitted angular mode is integrable and has the Fourier power bounds
up to the absolute discrete weight. -/
def RealDiscreteAngularFourierBoundStatement : Prop :=
  ∀ (k : ℕ), k ≠ 0 → ∀ (j : ℤ), (∃ m : ℕ,
    j = ((k + 1 + 2 * m : ℕ) : ℤ) ∨ j = -((k + 1 + 2 * m : ℕ) : ℤ)) →
    ∀ η : ℝ, 0 ≤ η → η ≤ k →
      Integrable (angularKernel k j) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, ‖𝓕 (angularKernel k j) y‖ ≤ C * |y| ^ η

theorem realDiscreteAngularFourierBound : RealDiscreteAngularFourierBoundStatement := by
  intro k hk j ⟨m, hj⟩ η hη hηk
  exact angularKernel_fourier_bound k m hk hj hη hηk

end Langlands.Global.RankinSelbergGlobal.RealDiscreteReciprocalFourier
