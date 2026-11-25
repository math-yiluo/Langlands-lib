/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Data.ZMod.Basic

/-!
# Alternating degree sums and alternating products of values

For a finite family of polynomials `P 0, …, P n` indexed by `Fin (n + 1)` this file defines the
alternating sum of their degrees and the alternating product of their values at a point. For a
family of Weil factors of a zeta function these are the Euler characteristic `χ` and the value
of the zeta function, but neither notion involves anything beyond polynomial algebra.

## Main definitions

- `Polynomial.alternatingNatDegreeSum`: the alternating sum `∑ᵢ (-1)ⁱ deg (P i)`.
- `Polynomial.alternatingProdEval`: the alternating product `∏ᵢ (P i) (t) ^ ((-1)^{i+1})`.

## Main results

- `Polynomial.even_alternatingNatDegreeSum_sub_of_natDegree_rev`: if the degrees of a family
  indexed by `Fin (2 * d + 1)` are invariant under `Fin.rev`, then the alternating degree sum
  has the same parity as the degree of the middle member.
-/

@[expose] public section

namespace Polynomial

/-- The alternating sum `∑ᵢ (-1)ⁱ deg (P i)` of the degrees of a finite family of polynomials.
For a family of Weil factors of a zeta function this is the Euler characteristic `χ` (blueprint
`definition-reciprocal-root`). -/
def alternatingNatDegreeSum {R : Type*} [Semiring R] {n : ℕ} (P : Fin (n + 1) → R[X]) : ℤ :=
  ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) * ((P i).natDegree : ℤ)

/-- The alternating product `∏ᵢ (P i) (t) ^ ((-1)^{i+1})` of the values of a finite family of
polynomials at `t`. For a family of Weil factors of a zeta function this is the value at `t` of
the rational function they cut out. -/
noncomputable def alternatingProdEval {K : Type*} [Field K] {n : ℕ} (P : Fin (n + 1) → K[X])
    (t : K) : K :=
  ∏ i : Fin (n + 1), (P i).eval t ^ ((-1 : ℤ) ^ ((i : ℕ) + 1))

/-- **Parity of an alternating degree sum with symmetric degrees.** If `deg (P i.rev)` and
`deg (P i)` agree for every `i`, then all the terms of `∑ᵢ (-1)ⁱ deg (P i)` except the one at
the unique fixed point `m` of `Fin.rev` cancel in pairs modulo `2`, so the alternating degree
sum has the same parity as `deg (P m)`. -/
theorem even_alternatingNatDegreeSum_sub_of_natDegree_rev {R : Type*} [Semiring R] {d : ℕ}
    {P : Fin (2 * d + 1) → R[X]} (hrev : ∀ i, (P i.rev).natDegree = (P i).natDegree)
    {m : Fin (2 * d + 1)} (hm : m.rev = m) :
    Even (alternatingNatDegreeSum P - ((P m).natDegree : ℤ)) := by
  classical
  have hmval : (m : ℕ) = d := by
    have := congrArg Fin.val hm
    simp only [Fin.val_rev] at this
    omega
  -- the unique fixed point of `Fin.rev` is `m`
  have hfix : ∀ i : Fin (2 * d + 1), i.rev = i → i = m := by
    intro i hi
    have := congrArg Fin.val hi
    simp only [Fin.val_rev] at this
    exact Fin.ext (by omega)
  set f : Fin (2 * d + 1) → ZMod 2 := fun i ↦ ((P i).natDegree : ZMod 2) with hf
  have hsum : ∑ i ∈ Finset.univ.erase m, f i = 0 := by
    refine Finset.sum_involution (fun i _ ↦ i.rev) (fun i _ ↦ ?_) (fun i hi _ ↦ ?_)
      (fun i hi ↦ ?_) (fun i _ ↦ Fin.rev_rev i)
    · simp only [hf, hrev i]
      exact CharTwo.add_self_eq_zero _
    · intro hcon
      exact (Finset.mem_erase.1 hi).1 (hfix i hcon)
    · refine Finset.mem_erase.2 ⟨fun hcon ↦ (Finset.mem_erase.1 hi).1 ?_, Finset.mem_univ _⟩
      rw [← Fin.rev_rev i, hcon, hm]
  have hcast : ((alternatingNatDegreeSum P : ℤ) : ZMod 2) = ∑ i : Fin (2 * d + 1), f i := by
    rw [alternatingNatDegreeSum]
    push_cast
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rcases Nat.even_or_odd (i : ℕ) with h | h
    · rw [h.neg_one_pow]
      simp [hf]
    · rw [h.neg_one_pow]
      simp [hf]
  refine even_iff_two_dvd.2 ?_
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd
    (alternatingNatDegreeSum P - ((P m).natDegree : ℤ)) 2).1 ?_
  · exact_mod_cast h
  · push_cast
    rw [hcast, ← Finset.sum_erase_add _ _ (Finset.mem_univ m), hsum, zero_add]
    simp [hf]

end Polynomial

end
