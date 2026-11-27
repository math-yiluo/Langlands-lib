import Langlands.Representation.Archimedean.OrthogonalGroupAveraging
import Langlands.Representation.Archimedean.OrthogonalHaarSmallBall
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt

/-! # First moment of a normalized polynomial peak on the orthogonal group -/

noncomputable section

open MeasureTheory Set
open scoped Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.OrthogonalHaar

local notation "O" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "M" n:max => Matrix (Fin n) (Fin n) ℝ

variable {n : ℕ}

theorem distSq_nonneg (x y : O n) : 0 ≤ distSq x y := by
  rw [distSq_eq_sum]
  positivity

theorem continuous_distSq_one : Continuous (fun x : O n => distSq x 1) := by
  simp only [distSq_eq_sum]
  refine continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun i _ => ?_
  have h : Continuous (fun x : O n => (x : M n) i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  exact (h.sub continuous_const).pow 2

/-- At the identity the squared distance is affine in the trace of the other matrix. -/
theorem distSq_one_eq_trace (x : O n) :
    distSq x 1 = 2 * ((n : ℝ) - Matrix.trace (x : M n)) := by
  have hs : Matrix.trace (star (x : M n)) = Matrix.trace (x : M n) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.star_apply, star_trivial]
  simp only [distSq, OneMemClass.coe_one, star_sub, star_one, sub_mul, mul_sub,
    Unitary.star_mul_self_of_mem x.prop, mul_one, one_mul, Matrix.trace_sub, Matrix.trace_one,
    Fintype.card_fin, hs]
  ring

/-- A degree-one polynomial peak on orthogonal matrices with value one at the identity. -/
def polynomialPeak (B : ℝ) (x : O n) : ℝ := 1 - distSq x 1 / (2 * B)

theorem continuous_polynomialPeak (B : ℝ) : Continuous (polynomialPeak (n := n) B) :=
  continuous_const.sub (continuous_distSq_one.div_const _)

/-- Compactness supplies a parameter for which the polynomial peak is everywhere positive. -/
theorem exists_polynomialPeak_parameter (n : ℕ) :
    ∃ B : ℝ, 0 < B ∧ (n : ℝ) ^ 2 ≤ B ∧ ∀ x : O n, distSq x 1 ≤ B := by
  obtain ⟨b, hb⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_distSq_one (n := n)).continuousOn
  refine ⟨max 1 (max ((n : ℝ) ^ 2) b), lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    (le_max_left _ _).trans (le_max_right _ _), fun x => ?_⟩
  exact (le_abs_self _).trans ((hb x (mem_univ x)).trans
    ((le_max_right _ _).trans (le_max_right _ _)))

private theorem gaussian_absorbs_polynomial {c t : ℝ} (hc : 0 < c) (ht : 1 ≤ t) (d : ℕ) :
    (2 * t ^ 4 + 1) ^ d * Real.exp (-(c * t ^ 2)) * t ≤
      3 ^ d * ((2 * d + 1).factorial : ℝ) / c ^ (2 * d + 1) := by
  let q := 2 * d + 1
  have ht₀ : 0 ≤ t := zero_le_one.trans ht
  have hq : 4 * d + 2 = 2 * q := by dsimp [q]; omega
  have hfac : 0 < (q.factorial : ℝ) := by positivity
  have hp := (div_le_iff₀ hfac).mp (Real.pow_div_factorial_le_exp (x := c * t ^ 2) (by positivity) q)
  rw [mul_pow, ← pow_mul, ← hq] at hp
  have hexp : t ^ (4 * d + 2) * Real.exp (-(c * t ^ 2)) ≤ (q.factorial : ℝ) / c ^ q := by
    apply (le_div_iff₀ (by positivity)).mpr
    rw [Real.exp_neg]
    calc
      _ = (c ^ q * t ^ (4 * d + 2)) / Real.exp (c * t ^ 2) := by rw [div_eq_mul_inv]; ring
      _ ≤ _ := (div_le_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using hp)
  have hpoly : (2 * t ^ 4 + 1) ^ d ≤ 3 ^ d * t ^ (4 * d) := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [one_le_pow₀ ht (n := 4)]) _
  have hts : t ≤ t ^ 2 := by nlinarith
  calc
    _ ≤ (3 ^ d * t ^ (4 * d)) * Real.exp (-(c * t ^ 2)) * t ^ 2 := by gcongr
    _ = 3 ^ d * (t ^ (4 * d + 2) * Real.exp (-(c * t ^ 2))) := by rw [pow_add]; ring
    _ ≤ _ := by rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-- For an allowable peak parameter, the normalized Haar first moment of the polynomial
peak of degree `t^4` decays at least as fast as `1/t`. -/
def OrthogonalPolynomialPeakMomentStatement : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (O n)] [BorelSpace (O n)] [MeasurableMul (O n)]
    (μ : Measure (O n)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (B : ℝ), 0 < n → 0 < B → (n : ℝ) ^ 2 ≤ B → (∀ x : O n, distSq x 1 ≤ B) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℕ, 0 < t →
      let Z := ∫ x : O n, polynomialPeak B x ^ (t ^ 4) ∂μ
      0 < Z ∧
        (∫ x : O n, Real.sqrt (distSq x 1) * polynomialPeak B x ^ (t ^ 4) ∂μ) / Z ≤ C / t

/-- A small Haar ball supplies the normalizing mass. The complementary region has a
pointwise Gaussian bound on the peak. -/
theorem orthogonalPolynomialPeakMoment : OrthogonalPolynomialPeakMomentStatement := by
  intro n _ _ _ μ _ _ B hn hB hdim hmax
  let d := n * n
  let c : ℝ := (n : ℝ) ^ 2 / (2 * B)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hc : 0 < c := by dsimp [c]; positivity
  let C₀ := (3 : ℝ) ^ d * ((2 * d + 1).factorial : ℝ) / c ^ (2 * d + 1)
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  refine ⟨(n : ℝ) + 2 * Real.sqrt B * C₀, by positivity, ?_⟩
  intro t ht
  let s := t ^ 4
  let f (x : O n) := polynomialPeak B x ^ s
  let Z := ∫ x, f x ∂μ
  let Q := ((2 * s + 1 : ℕ) : ℝ) ^ d
  let T := Real.exp (-(c * (t : ℝ) ^ 2))
  let S : Set (O n) := {x | distSq x 1 ≤ ((n : ℝ) / s) ^ 2}
  let J (x : O n) := Real.sqrt (distSq x 1) * f x
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  have ht₁ : 1 ≤ (t : ℝ) := by exact_mod_cast ht
  have hs : 0 < s := pow_pos ht _
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hs₁ : 1 ≤ (s : ℝ) := by exact_mod_cast hs
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hpeak (x : O n) : (1 / 2 : ℝ) ≤ polynomialPeak B x := by
    have hh : distSq x 1 / (2 * B) ≤ 1 / 2 :=
      (div_le_iff₀ (by positivity)).mpr (by linarith [hmax x])
    unfold polynomialPeak
    linarith
  have hf₀ (x : O n) : 0 ≤ f x := pow_nonneg (by linarith [hpeak x]) _
  have hfcont : Continuous f := (continuous_polynomialPeak B).pow s
  have hfi : Integrable f μ := hfcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hJi : Integrable J μ :=
    (continuous_distSq_one.sqrt.mul hfcont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hS : MeasurableSet S := (isClosed_le continuous_distSq_one continuous_const).measurableSet
  have hSlower (x : O n) (hx : x ∈ S) : (1 / 2 : ℝ) ≤ f x := by
    change distSq x 1 ≤ ((n : ℝ) / s) ^ 2 at hx
    have hh : (s : ℝ) * (distSq x 1 / (2 * B)) ≤ 1 / 2 := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity)).mpr
      calc
        (s : ℝ) * distSq x 1 ≤ (s : ℝ) * ((n : ℝ) / s) ^ 2 :=
          mul_le_mul_of_nonneg_left hx hsR.le
        _ = (n : ℝ) ^ 2 / s := by field_simp
        _ ≤ (n : ℝ) ^ 2 := div_le_self (by positivity) hs₁
        _ ≤ B := hdim
        _ = 1 / 2 * (2 * B) := by ring
    have hBern := one_add_mul_sub_le_pow (a := polynomialPeak B x) (by linarith [hpeak x]) s
    have hp : polynomialPeak B x - 1 = -(distSq x 1 / (2 * B)) := by
      unfold polynomialPeak
      ring
    rw [hp] at hBern
    exact (by linarith : (1 / 2 : ℝ) ≤ 1 + (s : ℝ) * -(distSq x 1 / (2 * B))).trans hBern
  have hM : 1 / Q ≤ μ.real S := orthogonalHaarSmallBall n μ s hs
  have hZ₀ : 1 / (2 * Q) ≤ Z := by
    calc
      _ = (1 / 2 : ℝ) * (1 / Q) := by field_simp
      _ ≤ (1 / 2 : ℝ) * μ.real S := by gcongr
      _ = ∫ _ in S, (1 / 2 : ℝ) ∂μ := by rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ ∫ x in S, f x ∂μ :=
        setIntegral_mono_on (integrable_const _).integrableOn hfi.integrableOn hS hSlower
      _ ≤ Z := setIntegral_le_integral hfi (Filter.Eventually.of_forall hf₀)
  have hZ : 0 < Z := (by positivity : 0 < 1 / (2 * Q)).trans_le hZ₀
  have hmass : 1 ≤ 2 * Q * Z := by
    rw [mul_comm (2 * Q)]
    exact (div_le_iff₀ (by positivity)).mp hZ₀
  have hFar (x : O n) (hx : ((n : ℝ) / t) ^ 2 ≤ distSq x 1) : f x ≤ T := by
    have hbase : polynomialPeak B x ≤ Real.exp (-(distSq x 1 / (2 * B))) := by
      simpa only [polynomialPeak, sub_eq_add_neg, add_comm] using
        Real.add_one_le_exp (-(distSq x 1 / (2 * B)))
    calc
      f x ≤ Real.exp (-(distSq x 1 / (2 * B))) ^ s :=
        pow_le_pow_left₀ (by linarith [hpeak x]) hbase _
      _ = Real.exp (-((s : ℝ) * distSq x 1 / (2 * B))) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ T := by
        apply Real.exp_le_exp.mpr
        apply neg_le_neg
        calc
          c * (t : ℝ) ^ 2 = (s : ℝ) * (((n : ℝ) / t) ^ 2) / (2 * B) := by
            dsimp only [c, s]
            rw [Nat.cast_pow]
            field_simp
          _ ≤ (s : ℝ) * distSq x 1 / (2 * B) := by gcongr
  have hJ (x : O n) : J x ≤ ((n : ℝ) / t) * f x + Real.sqrt B * T := by
    by_cases hx : distSq x 1 ≤ ((n : ℝ) / t) ^ 2
    · have hsqrt : Real.sqrt (distSq x 1) ≤ (n : ℝ) / t := by
        apply (Real.sqrt_le_iff).2
        exact ⟨by positivity, hx⟩
      exact (mul_le_mul_of_nonneg_right hsqrt (hf₀ x)).trans (le_add_of_nonneg_right (by
        dsimp [T]
        positivity))
    · exact (mul_le_mul (Real.sqrt_le_sqrt (hmax x)) (hFar x (le_of_not_ge hx))
        (hf₀ x) (Real.sqrt_nonneg B)).trans
        (le_add_of_nonneg_left (mul_nonneg (by positivity) (hf₀ x)))
  have hnum : (∫ x, J x ∂μ) ≤ ((n : ℝ) / t) * Z + Real.sqrt B * T := by
    have hi : Integrable (fun x => ((n : ℝ) / t) * f x) μ := hfi.const_mul _
    calc
      _ ≤ ∫ x : O n, ((n : ℝ) / t) * f x + Real.sqrt B * T ∂μ :=
        integral_mono hJi (hi.add (integrable_const _)) hJ
      _ = _ := by rw [integral_add hi (integrable_const _), integral_const_mul, integral_const,
        probReal_univ, one_smul]
  have hQtail : Q * T ≤ C₀ / t := by
    apply (le_div_iff₀ htR).mpr
    simpa only [Q, T, C₀, s, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
      using gaussian_absorbs_polynomial hc ht₁ d
  have htail : Real.sqrt B * T ≤ (2 * Real.sqrt B * C₀ / t) * Z := by
    calc
      _ ≤ (2 * Q * Z) * (Real.sqrt B * T) := le_mul_of_one_le_left (by
        dsimp [T]
        positivity) hmass
      _ = 2 * Real.sqrt B * Z * (Q * T) := by ring
      _ ≤ 2 * Real.sqrt B * Z * (C₀ / t) := by gcongr
      _ = _ := by ring
  change 0 < Z ∧ (∫ x, J x ∂μ) / Z ≤ ((n : ℝ) + 2 * Real.sqrt B * C₀) / t
  refine ⟨hZ, (div_le_iff₀ hZ).mpr (hnum.trans ?_)⟩
  rw [add_div, add_mul]
  exact add_le_add le_rfl htail

end Langlands.Archimedean.OrthogonalHaar
