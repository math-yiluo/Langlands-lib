/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.Reverse

/-!
# Complements on the reversal of a polynomial

## Main results

- `Polynomial.reverse_reverse` — reversal is an involution on polynomials with nonzero constant
  coefficient.
- `Polynomial.reverse_map` — reversal commutes with the coefficient map along an injective ring
  homomorphism.
- `Polynomial.monic_reverse_of_coeff_zero_eq_one` — the reverse of a polynomial with constant
  coefficient `1` is monic.
- `Polynomial.reverse_prod_of_domain` — over a domain, reversal is multiplicative on finite
  products.
- `Polynomial.reverse_multiset_prod_X_sub_C` — the reverse of a product `∏ (X - aᵢ)` of monic
  linear factors is `∏ (1 - aᵢ * X)`.
-/

@[expose] public section

namespace Polynomial

section Semiring

variable {R S : Type*} [Semiring R] [Semiring S]

/-- Reversing twice is the identity on polynomials with vanishing trailing degree, i.e. on
polynomials with nonzero constant coefficient. -/
theorem reverse_reverse {p : R[X]} (hp : p.natTrailingDegree = 0) : p.reverse.reverse = p := by
  have h : p.reverse.natDegree = p.natDegree := by rw [reverse_natDegree, hp, Nat.sub_zero]
  change reflect p.reverse.natDegree p.reverse = p
  rw [h]
  exact reflect_reflect

/-- Reversal commutes with the coefficient map along an injective ring homomorphism. -/
theorem reverse_map {f : R →+* S} (hf : Function.Injective f) (p : R[X]) :
    (p.map f).reverse = p.reverse.map f := by
  simp only [reverse, reflect_map, natDegree_map_eq_of_injective hf]

/-- The reverse of a polynomial with constant coefficient `1` is monic. -/
theorem monic_reverse_of_coeff_zero_eq_one [Nontrivial R] {p : R[X]} (hp : p.coeff 0 = 1) :
    p.reverse.Monic := by
  rw [Monic, reverse_leadingCoeff, trailingCoeff_eq_coeff_zero (by rw [hp]; exact one_ne_zero),
    hp]

end Semiring

variable {R : Type*} [CommRing R]

@[simp]
theorem reverse_X_sub_C (a : R) : (X - C a).reverse = 1 - C a * X := by
  nontriviality R
  have h1 : (1 : R[X]).reverse = 1 := by simpa using reverse_C (1 : R)
  have hX : (X : R[X]).reverse = 1 := by simpa [h1] using reverse_mul_X (1 : R[X])
  rw [sub_eq_add_neg, ← C_neg, reverse_add_C, hX, natDegree_X, pow_one, C_neg, sub_eq_add_neg,
    neg_mul]

/-- The reverse of a product of monic linear factors `∏ (X - a)` is `∏ (1 - a * X)`. -/
theorem reverse_multiset_prod_X_sub_C [NoZeroDivisors R] (s : Multiset R) :
    ((s.map fun a ↦ X - C a).prod).reverse = (s.map fun a ↦ 1 - C a * X).prod := by
  induction s using Multiset.induction with
  | empty => simpa using reverse_C (1 : R)
  | cons a s ih => simp [ih]

/-- Over a domain, the reverse of a finite product is the product of the reverses. -/
theorem reverse_prod_of_domain [NoZeroDivisors R] {ι : Type*} (s : Finset ι) (f : ι → R[X]) :
    (∏ i ∈ s, f i).reverse = ∏ i ∈ s, (f i).reverse := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using reverse_C (1 : R)
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, reverse_mul_of_domain, ih]

end Polynomial
