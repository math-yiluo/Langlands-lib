import Langlands.LinearAlgebra.UnipotentBinomialStatement

/-! # Proof of the finite binomial expansions for unipotent operators -/

namespace Langlands

universe u

open Polynomial

/-- Generalized complex binomial coefficients are evaluations of the
factorial-normalized descending Pochhammer polynomial. -/
theorem complexBinomialCoefficientPolynomial :
    ComplexBinomialCoefficientPolynomialStatement := by
  intro j z
  rw [Ring.choose_eq_smul, eval_smul]
  congr 1
  rw [← descPochhammer_map (Int.castRingHom ℂ), eval_map,
    ← eval₂_smulOneHom_eq_smeval ℤ]
  congr 1
  exact Subsingleton.elim _ _

/-- Pascal's rule for a truncated binomial sum: if `N ^ r = 0`, right
multiplication by `1 + N` raises the complex exponent by one. -/
theorem truncatedBinomialSum_mul_one_add {A : Type*} [Ring A] [Module ℂ A]
    [IsScalarTower ℂ A A] (N : A) (r : ℕ) (hN : N ^ r = 0) (z : ℂ) :
    (∑ j ∈ Finset.range r, Ring.choose z j • N ^ j) * (1 + N) =
      ∑ j ∈ Finset.range r, Ring.choose (z + 1) j • N ^ j := by
  cases r with
  | zero => simp
  | succ r =>
    rw [mul_add, mul_one, Finset.sum_mul]
    simp_rw [smul_mul_assoc, ← pow_succ]
    rw [Finset.sum_range_succ (fun j => Ring.choose z j • N ^ (j + 1)), hN, smul_zero,
      add_zero, Finset.sum_range_succ' (fun j => Ring.choose z j • N ^ j),
      Finset.sum_range_succ' (fun j => Ring.choose (z + 1) j • N ^ j)]
    simp_rw [Ring.choose_succ_succ, add_smul, Ring.choose_zero_right]
    rw [Finset.sum_add_distrib]
    abel

/-- Every integer power of a unit `g` of `Module.End ℂ V` with `(g - 1) ^ r = 0`
is the truncated generalized binomial sum in `g - 1`. -/
theorem integerUnipotentBinomial : IntegerUnipotentBinomialStatement.{u} := by
  intro V _ _ g r hr n
  generalize hN : (g : Module.End ℂ V) - 1 = N at hr ⊢
  have hg : (g : Module.End ℂ V) = 1 + N := by
    rw [← hN]
    abel
  have step (z : ℂ) : (∑ j ∈ Finset.range r, Ring.choose z j • N ^ j) * g =
      ∑ j ∈ Finset.range r, Ring.choose (z + 1) j • N ^ j := by
    rw [hg]
    exact truncatedBinomialSum_mul_one_add N r hr z
  induction n with
  | zero =>
    rw [zpow_zero, Units.val_one, Int.cast_zero]
    cases r with
    | zero =>
      rw [pow_zero] at hr
      simp [hr]
    | succ r =>
      rw [Finset.sum_range_succ', Ring.choose_zero_right, pow_zero, one_smul]
      simp only [Ring.choose_zero_succ, zero_smul, Finset.sum_const_zero, zero_add]
  | succ k ih =>
    rw [zpow_add_one, Units.val_mul, ih, step, Int.cast_add, Int.cast_one]
  | pred k ih =>
    have h := step ((-(k : ℤ) - 1 : ℤ) : ℂ)
    rw [show ((-(k : ℤ) - 1 : ℤ) : ℂ) + 1 = ((-(k : ℤ) : ℤ) : ℂ) by push_cast; ring,
      ← ih] at h
    rw [zpow_sub_one, Units.val_mul, ← h, mul_assoc, Units.mul_inv, mul_one]

/-- Both auxiliary assertions of the Renard C.III proof. -/
theorem renardCIIIUnipotentBinomial : RenardCIIIUnipotentBinomialStatement.{u} :=
  ⟨integerUnipotentBinomial, complexBinomialCoefficientPolynomial⟩

end Langlands
