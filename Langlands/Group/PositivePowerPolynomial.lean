import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! # Polynomial vanishing along nonnegative real powers -/

noncomputable section

universe u v

namespace Langlands.Group.PositivePowerPolynomial

open scoped BigOperators

/-- A finite weighted sum that annihilates every natural monomial also
annihilates any function of the same finitely many arguments. -/
theorem sum_mul_apply_eq_zero_of_moments
    {K : Type u} [Field K] {ι : Type v} (s : Finset ι) (a b : ι → K)
    (h : ∀ m : ℕ, ∑ i ∈ s, a i * b i ^ m = 0) (f : K → K) :
    ∑ i ∈ s, a i * f (b i) = 0 := by
  classical
  have hp (p : Polynomial K) : ∑ i ∈ s, a i * p.eval (b i) = 0 := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      simp only [Polynomial.eval_add, mul_add, Finset.sum_add_distrib, hp, hq, add_zero]
    | monomial m c =>
      simp only [Polynomial.eval_monomial]
      calc
        ∑ i ∈ s, a i * (c * b i ^ m) =
            c * ∑ i ∈ s, a i * b i ^ m := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
        _ = 0 := by rw [h m, mul_zero]
  obtain ⟨p, hp_eval⟩ :=
    (Polynomial.exists_eval_eq_iff (fun i : s => b i) (fun i : s => f (b i))).mpr
      (fun i j hij => congrArg f hij)
  calc
    ∑ i ∈ s, a i * f (b i) = ∑ i ∈ s, a i * p.eval (b i) := by
      exact Finset.sum_congr rfl fun i hi => by rw [hp_eval ⟨i, hi⟩]
    _ = 0 := hp p

variable {𝕜 : Type u} [RCLike 𝕜] {σ : Type v}

/-- Coordinatewise real powers, viewed in an arbitrary real or complex field. -/
def powerPoint (x : σ → ℝ) (r : ℝ) : σ → 𝕜 :=
  fun i => RCLike.ofReal (x i ^ r)

private theorem eval_powerPoint (p : MvPolynomial σ 𝕜) (x : σ → ℝ)
    (hx : ∀ i, 0 ≤ x i) (r : ℝ) :
    MvPolynomial.eval (powerPoint x r) p =
      ∑ d ∈ p.support, p.coeff d *
        RCLike.ofReal ((∏ i ∈ d.support, x i ^ d i) ^ r) := by
  classical
  rw [MvPolynomial.eval_eq]
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  have hprod :
      (∏ i ∈ d.support, (powerPoint x r i : 𝕜) ^ d i) =
        RCLike.ofReal (∏ i ∈ d.support, (x i ^ r) ^ d i) := by
    simp only [powerPoint, RCLike.ofReal_prod, RCLike.ofReal_pow]
  rw [hprod]
  congr 1
  calc
    ∏ i ∈ d.support, (x i ^ r) ^ d i =
        ∏ i ∈ d.support, (x i ^ d i) ^ r := by
      exact Finset.prod_congr rfl fun i _ => Real.rpow_pow_comm (hx i) r (d i)
    _ = (∏ i ∈ d.support, x i ^ d i) ^ r :=
      Real.finsetProd_rpow d.support (fun i => x i ^ d i)
        (fun i _ => pow_nonneg (hx i) _) r

/-- If a polynomial vanishes at every coordinatewise natural power of a
nonnegative real point, it vanishes at every coordinatewise real power. -/
theorem eval_powerPoint_eq_zero
    (p : MvPolynomial σ 𝕜) (x : σ → ℝ) (hx : ∀ i, 0 ≤ x i)
    (h : ∀ m : ℕ, MvPolynomial.eval (powerPoint x (m : ℝ)) p = 0)
    (r : ℝ) :
    MvPolynomial.eval (powerPoint x r) p = 0 := by
  classical
  have hm (m : ℕ) :
      ∑ d ∈ p.support, p.coeff d *
        (RCLike.ofReal (∏ i ∈ d.support, x i ^ d i) : 𝕜) ^ m = 0 := by
    have hh := h m
    rw [eval_powerPoint p x hx] at hh
    simpa only [Real.rpow_natCast, RCLike.ofReal_pow] using hh
  rw [eval_powerPoint p x hx]
  have hs := sum_mul_apply_eq_zero_of_moments p.support p.coeff
    (fun d => (RCLike.ofReal (∏ i ∈ d.support, x i ^ d i) : 𝕜)) hm
    (fun z => (RCLike.ofReal ((RCLike.re z) ^ r) : 𝕜))
  simpa only [RCLike.ofReal_re] using hs

end Langlands.Group.PositivePowerPolynomial
