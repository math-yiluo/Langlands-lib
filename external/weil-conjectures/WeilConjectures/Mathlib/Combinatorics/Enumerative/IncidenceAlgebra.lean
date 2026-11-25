/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra

/-!
# Möbius components of a multiplicative family of idempotents

Let `α` be a lattice with a bottom element in which all intervals are finite, `R` a (not
necessarily commutative) ring and `π : α → R` a family with `π x * π y = π (x ⊓ y)` (for instance
the projectors onto the invariants of a family of normal subgroups). The *Möbius components*
`e k = ∑_{m ≤ k} μ(m, k) • π m` (`IncidenceAlgebra.moebiusComponent`) decompose the `π`:

* `∑_{k ≤ j} e k = π j` (`IncidenceAlgebra.sum_Iic_moebiusComponent`, by Möbius inversion);
* `e k * π m = e k` if `k ≤ m` and `0` otherwise (`IncidenceAlgebra.moebiusComponent_mul`), and
  similarly `π m * e k` (`IncidenceAlgebra.mul_moebiusComponent`);
* `e ⊥ = π ⊥` (`IncidenceAlgebra.moebiusComponent_bot`).

In particular the `e k` are orthogonal idempotents.
-/

@[expose] public section

open Finset

namespace IncidenceAlgebra

variable {α R : Type*} [Lattice α] [OrderBot α] [LocallyFiniteOrder α] [DecidableEq α] [Ring R]

/-- The **Möbius component** `e k = ∑_{m ≤ k} μ(m, k) • π m` of a family `π : α → R`. -/
def moebiusComponent (π : α → R) (k : α) : R :=
  ∑ m ∈ Iic k, mu ℤ m k • π m

/-- **Möbius inversion**: the Möbius components below `j` sum to `π j`. -/
lemma sum_Iic_moebiusComponent (π : α → R) (j : α) :
    ∑ k ∈ Iic j, moebiusComponent π k = π j := by
  unfold moebiusComponent
  rw [sum_comm' (t' := Iic j) (s' := fun m ↦ Icc m j) (fun k m ↦ by
    simp only [mem_Iic, mem_Icc]
    exact ⟨fun h ↦ ⟨⟨h.2, h.1⟩, h.2.trans h.1⟩, fun h ↦ ⟨h.1.2, h.1.1⟩⟩)]
  simp_rw [← sum_smul, sum_Icc_mu_right, ite_smul, one_smul, zero_smul]
  rw [sum_ite_eq' (Iic j) j, ite_eq_left (mem_Iic.2 le_rfl)]

/-- The Möbius component `e k` is `π k` minus the components strictly below `k`. -/
lemma moebiusComponent_eq_sub (π : α → R) (k : α) :
    moebiusComponent π k = π k - ∑ x ∈ Iio k, moebiusComponent π x := by
  rw [eq_sub_iff_add_eq, ← sum_Iic_moebiusComponent π k, ← Iio_insert,
    sum_insert (fun h ↦ (lt_irrefl k (mem_Iio.1 h)))]

/-- The Möbius component at the bottom element is `π ⊥`. -/
lemma moebiusComponent_bot (π : α → R) : moebiusComponent π ⊥ = π ⊥ := by
  rw [moebiusComponent_eq_sub, Iio_bot, sum_empty, sub_zero]

/-- An additive map commutes with the Möbius components. -/
lemma map_moebiusComponent {S : Type*} [AddCommGroup S] (f : R →+ S) (π : α → R) (k : α) :
    f (moebiusComponent π k) = ∑ m ∈ Iic k, mu ℤ m k • f (π m) := by
  simp only [moebiusComponent, map_sum, map_zsmul]

variable {π : α → R}

/-- The Möbius components commute with the family `π`. -/
lemma moebiusComponent_mul_comm (hπ : ∀ x y, π x * π y = π (x ⊓ y)) (k m : α) :
    moebiusComponent π k * π m = π m * moebiusComponent π k := by
  simp only [moebiusComponent, sum_mul, mul_sum, smul_mul_assoc, mul_smul_comm, hπ, inf_comm]

variable [DecidableLE α]

/-- **Orthogonality of the Möbius components**: `e k * π m` is `e k` if `k ≤ m`, and `0`
otherwise. -/
lemma moebiusComponent_mul (hπ : ∀ x y, π x * π y = π (x ⊓ y)) (k m : α) :
    moebiusComponent π k * π m = if k ≤ m then moebiusComponent π k else 0 := by
  induction hn : (Iic k).card using Nat.strong_induction_on generalizing k with
  | _ n ih =>
  have ih' : ∀ x ∈ Iio k, moebiusComponent π x * π m =
      if x ≤ m then moebiusComponent π x else 0 := fun x hx ↦
    ih _ (hn ▸ card_lt_card (Iic_ssubset_Iic.2 (mem_Iio.1 hx))) x rfl
  rw [moebiusComponent_eq_sub, sub_mul, sum_mul, sum_congr rfl ih', ← sum_filter, hπ]
  split_ifs with hkm
  · rw [inf_eq_left.2 hkm, filter_true_of_mem fun x hx ↦
      (mem_Iio.1 hx).le.trans hkm]
  · have : (Iio k).filter (· ≤ m) = Iic (k ⊓ m) := by
      ext x
      simp only [mem_filter, mem_Iio, mem_Iic, le_inf_iff]
      exact ⟨fun h ↦ ⟨h.1.le, h.2⟩, fun h ↦ ⟨lt_of_le_of_ne h.1 fun hx ↦ hkm (hx ▸ h.2), h.2⟩⟩
    rw [this, sum_Iic_moebiusComponent, sub_self]

/-- **Orthogonality of the Möbius components**: `π m * e k` is `e k` if `k ≤ m`, and `0`
otherwise. -/
lemma mul_moebiusComponent (hπ : ∀ x y, π x * π y = π (x ⊓ y)) (k m : α) :
    π m * moebiusComponent π k = if k ≤ m then moebiusComponent π k else 0 := by
  rw [← moebiusComponent_mul_comm hπ, moebiusComponent_mul hπ]

end IncidenceAlgebra
