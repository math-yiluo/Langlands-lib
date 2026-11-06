import Langlands.Representation.RankinSelberg.PairLFactorCharacterizationStatement

/-!
# Arithmetic of pole orders at `s = 0`

The order `lPolynomialPoleOrderAtZero P` of the pole at `s = 0` of
`L(s) = 1 / P(q^(-s))` is the multiplicity of `1` as a root of `P`. It is
additive on products of normalized polynomials, and the polynomial
`∏_(a ∈ A) (1 - a X)` of JPSS 1983, Proposition (8.1)(ii), has pole order one
at `s = 0` exactly when `1 ∈ A`, and zero otherwise.
-/

noncomputable section

namespace Langlands.RankinSelberg

open Polynomial

/-- A polynomial with constant coefficient `1` is nonzero. -/
theorem ne_zero_of_coeff_zero_eq_one {P : ℂ[X]} (h : P.coeff 0 = 1) : P ≠ 0 := by
  rintro rfl
  simp at h

/-- The pole order at `s = 0` of a product of two nonzero polynomials is the sum
of the pole orders. -/
theorem lPolynomialPoleOrderAtZero_mul {P Q : ℂ[X]} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    lPolynomialPoleOrderAtZero (P * Q) =
      lPolynomialPoleOrderAtZero P + lPolynomialPoleOrderAtZero Q :=
  rootMultiplicity_mul (mul_ne_zero hP hQ)

/-- The pole order at `s = 0` of a finite product of nonzero polynomials is the
sum of the pole orders. -/
theorem lPolynomialPoleOrderAtZero_prod {ι : Type*} (s : Finset ι) (P : ι → ℂ[X])
    (h : ∀ i ∈ s, P i ≠ 0) :
    lPolynomialPoleOrderAtZero (∏ i ∈ s, P i) =
      ∑ i ∈ s, lPolynomialPoleOrderAtZero (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [lPolynomialPoleOrderAtZero]
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj,
      lPolynomialPoleOrderAtZero_mul (h j (Finset.mem_insert_self j s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

/-- The pole order at `s = 0` of a double product over finite types of
polynomials with constant coefficient `1` is the double sum of the pole orders. -/
theorem lPolynomialPoleOrderAtZero_prod_prod {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Q : ι → κ → ℂ[X]) (h : ∀ i j, (Q i j).coeff 0 = 1) :
    lPolynomialPoleOrderAtZero (∏ i, ∏ j, Q i j) =
      ∑ i, ∑ j, lPolynomialPoleOrderAtZero (Q i j) := by
  have hQ : ∀ i j, Q i j ≠ 0 := fun i j => ne_zero_of_coeff_zero_eq_one (h i j)
  rw [lPolynomialPoleOrderAtZero_prod _ _ fun i _ =>
    Finset.prod_ne_zero_iff.mpr fun j _ => hQ i j]
  exact Finset.sum_congr rfl fun i _ =>
    lPolynomialPoleOrderAtZero_prod _ _ fun j _ => hQ i j

/-- The factor `1 - a X` has pole order one at `s = 0` when `a = 1`, and zero
otherwise. -/
theorem lPolynomialPoleOrderAtZero_one_sub_C_mul_X (a : ℂ) :
    lPolynomialPoleOrderAtZero (1 - C a * X) = if a = 1 then 1 else 0 := by
  unfold lPolynomialPoleOrderAtZero
  split_ifs with ha
  · subst ha
    have : (1 - C (1 : ℂ) * X : ℂ[X]) = (X - C 1) * C (-1) := by
      simp only [map_one, one_mul, map_neg, mul_neg, mul_one, neg_sub]
    rw [this, rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero 1) (by simp)),
      rootMultiplicity_X_sub_C_self, rootMultiplicity_C, add_zero]
  · apply rootMultiplicity_eq_zero
    simp only [IsRoot, eval_sub, eval_one, eval_mul, eval_C, eval_X, mul_one]
    exact sub_ne_zero.mpr (Ne.symm ha)

/-- JPSS 1983, Proposition (8.1)(ii) form: `∏_(a ∈ A) (1 - a X)` has pole order
one at `s = 0` exactly when `1 ∈ A`, and zero otherwise. -/
theorem lPolynomialPoleOrderAtZero_prod_one_sub_C_mul_X (A : Finset ℂ) :
    lPolynomialPoleOrderAtZero (∏ a ∈ A, (1 - C a * X)) = if (1 : ℂ) ∈ A then 1 else 0 := by
  rw [lPolynomialPoleOrderAtZero_prod _ _ fun a _ =>
    ne_zero_of_coeff_zero_eq_one (by simp)]
  simp_rw [lPolynomialPoleOrderAtZero_one_sub_C_mul_X]
  rw [Finset.sum_ite_eq' A 1 fun _ => 1]

end Langlands.RankinSelberg
