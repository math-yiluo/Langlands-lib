import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Rename

/-! # Functions on `ℕ ^ n` that are polynomial along coordinate lines

A function `f : (Fin n → ℕ) → K` that is given by a one-variable polynomial of bounded degree
along every coordinate line is the restriction of a multivariate polynomial.
-/

noncomputable section

open Polynomial

namespace Langlands.Algebra.DegreeDeterminant

variable {K : Type*} [Field K] [CharZero K]

/-- A polynomial of degree at most `D` is determined by its values at `0, …, D`, through
the Lagrange basis on these nodes. -/
theorem eval_eq_sum_lagrange (D : ℕ) (R : K[X]) (hR : R.natDegree ≤ D) (t : K) :
    R.eval t = ∑ k ∈ Finset.range (D + 1),
      R.eval (k : K) * (Lagrange.basis (Finset.range (D + 1)) (fun j : ℕ => (j : K)) k).eval t := by
  have hinj : Set.InjOn (fun j : ℕ => (j : K)) (Finset.range (D + 1) : Set ℕ) :=
    fun a _ b _ h => Nat.cast_injective h
  have hdeg : R.degree < (Finset.range (D + 1)).card := by
    rw [Finset.card_range]
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hR)
  conv_lhs => rw [Lagrange.eq_interpolate hinj hdeg]
  rw [Lagrange.interpolate_apply, eval_finsetSum]
  simp only [eval_mul, eval_C]

omit [CharZero K] in
/-- Evaluating a one-variable polynomial in the variable `X i`. -/
theorem eval_aeval_X {n : ℕ} (v : Fin n → K) (i : Fin n) (p : K[X]) :
    MvPolynomial.eval v (Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) K) p) =
      p.eval (v i) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial k a => simp [Polynomial.aeval_monomial]

/-- Separately polynomial functions on `ℕ ^ n` are restrictions of multivariate
polynomials. -/
theorem exists_mvPolynomial_of_line (D : ℕ) :
    ∀ (n : ℕ) (f : (Fin n → ℕ) → K),
      (∀ (i : Fin n) (x : Fin n → ℕ), ∃ R : K[X], R.natDegree ≤ D ∧
        ∀ m : ℕ, f (Function.update x i (x i + m)) = R.eval (m : K)) →
      ∃ M : MvPolynomial (Fin n) K,
        ∀ x : Fin n → ℕ, f x = MvPolynomial.eval (fun i => (x i : K)) M := by
  intro n
  induction n with
  | zero =>
    intro f _
    refine ⟨MvPolynomial.C (f Fin.elim0), fun x => ?_⟩
    rw [MvPolynomial.eval_C]
    congr 1
    exact funext fun i => Fin.elim0 i
  | succ n ih =>
    intro f hf
    have hg : ∀ k : ℕ, ∀ (i : Fin n) (x : Fin n → ℕ), ∃ R : K[X], R.natDegree ≤ D ∧
        ∀ m : ℕ, f (Fin.cons k (Function.update x i (x i + m))) = R.eval (m : K) := by
      intro k i x
      obtain ⟨R, hR, hRe⟩ := hf i.succ (Fin.cons k x)
      refine ⟨R, hR, fun m => ?_⟩
      rw [← hRe m, Fin.cons_update, Fin.cons_succ]
    choose M hM using fun k : ℕ => ih (fun x => f (Fin.cons k x)) (hg k)
    let B : ℕ → K[X] := fun k =>
      Lagrange.basis (Finset.range (D + 1)) (fun j : ℕ => (j : K)) k
    refine ⟨∑ k ∈ Finset.range (D + 1),
      Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin (n + 1)) K) (B k) *
        MvPolynomial.rename Fin.succ (M k), fun x => ?_⟩
    obtain ⟨R, hR, hRe⟩ := hf 0 (Fin.cons 0 (Fin.tail x))
    have hline : ∀ m : ℕ, f (Fin.cons m (Fin.tail x)) = R.eval (m : K) := by
      intro m
      rw [← hRe m, Fin.cons_zero, zero_add, Fin.update_cons_zero]
    rw [← Fin.cons_self_tail x, hline, eval_eq_sum_lagrange D R hR, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hline k, hM k, map_mul, MvPolynomial.eval_rename, mul_comm]
    congr 1
    rw [eval_aeval_X]
    rfl

end Langlands.Algebra.DegreeDeterminant
