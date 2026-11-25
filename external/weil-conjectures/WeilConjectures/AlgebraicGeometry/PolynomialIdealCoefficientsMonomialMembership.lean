/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.MvPolynomial.Basic

@[expose] public section

universe u

open MvPolynomial

namespace MvPolynomial

/-- Coefficient membership criterion for the coordinate ideal.
Source: literature/stacks-project/algebra.tex, proof of Lemma Tag 07DW.
(blueprint: new-polynomial-ideal-coefficients-membership)
The proof follows the coefficient comparison and finite monomial decomposition in the
source: coefficients of each generator product are multiples of the corresponding
`g`, and conversely each coefficient in the indicated span is expanded into such
multiples and its monomial is factored by the relevant variable. -/
theorem ideal_coefficients_monomial_membership
    {R : Type u} [CommRing R] (r i : ℕ) (hr : 1 ≤ r) (hir : i ≤ r)
    (g : Fin i → R)
    (p : MvPolynomial (Fin r) R) :
    p ∈ Ideal.span (Set.range fun j : Fin i => C (g j) * X (Fin.castLE hir j)) ↔
      ∀ E : Fin r →₀ ℕ,
        AddMonoidAlgebra.coeff p E ∈ Ideal.span (g '' {j : Fin i | E (Fin.castLE hir j) ≠ 0}) := by
  classical
  have _ := hr
  let J : Ideal (MvPolynomial (Fin r) R) :=
    Ideal.span (Set.range fun j : Fin i => C (g j) * X (Fin.castLE hir j))
  constructor
  · intro hp E
    obtain ⟨q, hq⟩ := Ideal.mem_span_range_iff_exists_fun.mp hp
    rw [← hq, coeff_sum]
    apply Submodule.sum_mem
    intro j _
    rw [mul_comm (q j), mul_assoc, coeff_C_mul, coeff_X_mul']
    split_ifs with hE
    · apply Ideal.mul_mem_right
      exact Ideal.subset_span ⟨j, by simpa using hE, rfl⟩
    · simp
  · intro hp
    have hm : ∀ (E : Fin r →₀ ℕ) (c : R),
        c ∈ Ideal.span (g '' {j : Fin i | E (Fin.castLE hir j) ≠ 0}) →
        monomial E c ∈ J := by
      intro E c hc
      induction hc using Submodule.span_induction with
      | mem c hc =>
        obtain ⟨j, hj, rfl⟩ := hc
        have hle : Finsupp.single (Fin.castLE hir j) 1 ≤ E := by
          rw [Finsupp.single_le_iff]
          exact Nat.one_le_iff_ne_zero.mpr hj
        have heq : E - Finsupp.single (Fin.castLE hir j) 1 +
            Finsupp.single (Fin.castLE hir j) 1 = E := tsub_add_cancel_of_le hle
        have hgen : C (g j) * X (Fin.castLE hir j) ∈ J :=
          Ideal.subset_span ⟨j, rfl⟩
        convert J.mul_mem_left (monomial
          (E - Finsupp.single (Fin.castLE hir j) 1) 1) hgen using 1
        simp only [X, C_apply, monomial_mul_monomial]
        simp [heq]
      | zero => simp
      | add a b ha hb ia ib =>
        simpa only [map_add] using J.add_mem ia ib
      | smul a b hb ib =>
        simpa only [smul_eq_mul, ← C_mul_monomial] using J.mul_mem_left (C a) ib
    rw [p.as_sum]
    exact J.sum_mem fun E _ => hm E (AddMonoidAlgebra.coeff p E) (hp E)

end MvPolynomial
