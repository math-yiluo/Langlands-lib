import Langlands.Representation.Archimedean.RealTailMultiplierPolynomial
import Langlands.Representation.Archimedean.RealCompactPolynomialRelations
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Roots

/-! # Exact normalization of tail polynomials at compact generators -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.RealTailCompactPolynomialNormalization

open Polynomial Complex RealTailMultiplierPolynomial RealCompactPolynomialRelations

theorem tailPolynomial_step (n : ℕ) (z : ℂ) :
    4 * (n + 1 : ℂ) * (n + 2 : ℂ) * (tailPolynomial (n + 2)).eval z =
      (z ^ 2 - (n + 1 : ℂ) ^ 2) * (tailPolynomial n).eval z := by
  rw [tailPolynomial_eval, tailPolynomial_eval]
  have hdesc :
      (descPochhammer ℂ (n + 2)).eval ((z + (n + 2 : ℕ) - 1) / 2) =
        ((z + (n + 2 : ℕ) - 1) / 2) *
          (descPochhammer ℂ n).eval ((z + (n : ℂ) - 1) / 2) *
          (((z + (n + 2 : ℕ) - 1) / 2) - 1 - n) := by
    rw [show n + 2 = (n + 1) + 1 by omega, descPochhammer_succ_left]
    simp only [eval_mul, eval_X, eval_comp, eval_sub, eval_one]
    rw [descPochhammer_succ_eval]
    have he : (z + ((n + 1 + 1 : ℕ) : ℂ) - 1) / 2 - 1 =
        (z + (n : ℂ) - 1) / 2 := by push_cast; ring
    rw [he]
    ring
  rw [hdesc]
  have hfac : ((n + 2).factorial : ℂ) =
      (n + 2 : ℂ) * (n + 1 : ℂ) * (n.factorial : ℂ) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  rw [hfac]
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hn1 : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
  have hn2 : (n + 2 : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
  push_cast
  field_simp
  ring

/-- The exact scalar converting the normalized tail polynomial to the monic compact factor. -/
theorem eval_normalization (n : ℕ) (z : ℂ) :
    ((2 : ℂ) ^ n * (n.factorial : ℂ)) * (tailPolynomial n).eval (-I * z) =
      (-I : ℂ) ^ n * factor z n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [tailPolynomial_eval, factor]
  | one => simp [tailPolynomial_eval, factor]; ring
  | more n ih _ =>
    have hs := tailPolynomial_step n (-I * z)
    have hfac : ((n + 2).factorial : ℂ) =
        (n + 2 : ℂ) * (n + 1 : ℂ) * (n.factorial : ℂ) := by
      rw [Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    rw [hfac, pow_add, pow_add, factor]
    simp only [smul_eq_mul]
    norm_num only [pow_two, neg_mul, mul_neg, I_mul_I] at hs ⊢
    simp only [neg_mul] at ih
    linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring))
      ((2 : ℂ) ^ n * (n.factorial : ℂ)) * hs -
        (z ^ 2 + (n + 1 : ℂ) ^ 2) * ih

theorem aeval_factor {A : Type*} [Ring A] [Algebra ℂ A] (x : A) (n : ℕ) :
    aeval x (factor (X : ℂ[X]) n) = factor x n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [factor]
  | one => simp [factor]
  | more n ih _ =>
    simp only [factor, map_add, map_mul, map_smul, aeval_X, ih]

/-- Equality in the scalar polynomial ring before evaluation in any complex algebra. -/
theorem polynomial_normalization (n : ℕ) :
    C ((2 : ℂ) ^ n * (n.factorial : ℂ)) *
        (tailPolynomial n).comp (C (-I) * X) =
      C ((-I : ℂ) ^ n) * factor (X : ℂ[X]) n := by
  let : Infinite ℂ := Infinite.of_injective (fun m : ℕ => (m : ℂ)) Nat.cast_injective
  apply Polynomial.funext
  intro z
  have hf := aeval_factor z n
  simp only [coe_aeval_eq_eval] at hf
  simp only [eval_mul, eval_C, eval_comp, eval_X]
  rw [hf]
  exact eval_normalization n z

/-- The normalization applies to compact generators as operators, without commutativity. -/
theorem operator_normalization {A : Type*} [Ring A] [Algebra ℂ A] (x : A) (n : ℕ) :
    ((2 : ℂ) ^ n * (n.factorial : ℂ)) • aeval ((-I : ℂ) • x) (tailPolynomial n) =
      ((-I : ℂ) ^ n) • factor x n := by
  have hh := congrArg (fun P : ℂ[X] => aeval x P) (polynomial_normalization n)
  simpa only [map_mul, aeval_C, aeval_comp, aeval_factor, aeval_X,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_smul] using hh

theorem operator_eq_factor {A : Type*} [Ring A] [Algebra ℂ A] (x : A) (n : ℕ) :
    aeval ((-I : ℂ) • x) (tailPolynomial n) =
      ((-I : ℂ) ^ n / ((2 : ℂ) ^ n * (n.factorial : ℂ))) • factor x n := by
  have hc : (2 : ℂ) ^ n * (n.factorial : ℂ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast n.factorial_ne_zero)
  calc
    aeval ((-I : ℂ) • x) (tailPolynomial n) =
        (((2 : ℂ) ^ n * (n.factorial : ℂ))⁻¹) •
          (((2 : ℂ) ^ n * (n.factorial : ℂ)) •
            aeval ((-I : ℂ) • x) (tailPolynomial n)) := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = (((2 : ℂ) ^ n * (n.factorial : ℂ))⁻¹) •
        (((-I : ℂ) ^ n) • factor x n) :=
      congrArg (fun v : A => (((2 : ℂ) ^ n * (n.factorial : ℂ))⁻¹) • v)
        (operator_normalization x n)
    _ = _ := by rw [smul_smul, div_eq_mul_inv, mul_comm]

end Langlands.Archimedean.RealTailCompactPolynomialNormalization

namespace Langlands.Archimedean

open Polynomial Complex RealTailMultiplierPolynomial RealCompactPolynomialRelations in
/-- The exact noncommutative normalization of the differential tail polynomial. -/
def RealTailCompactPolynomialNormalizationStatement : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (x : A) (n : ℕ),
    ((2 : ℂ) ^ n * (n.factorial : ℂ)) • aeval ((-I : ℂ) • x) (tailPolynomial n) =
      ((-I : ℂ) ^ n) • factor x n

theorem realTailCompactPolynomialNormalization : RealTailCompactPolynomialNormalizationStatement :=
  fun _ _ _ x n => RealTailCompactPolynomialNormalization.operator_normalization x n

end Langlands.Archimedean
