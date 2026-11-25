/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Sums of additive characters

An additive character `ψ` of a finite group which takes, at some point `b`, a value with
`ψ(b) - 1` a unit sums to zero. Unlike `AddChar.sum_eq_zero_of_ne_one`, this holds for an
arbitrary commutative target ring.

## Main statements

- `AddChar.sum_eq_zero_of_isUnit_sub_one`: `∑_a ψ(a) = 0` if `ψ(b) - 1` is a unit.
- `AddChar.linearIndependent_coe`: Dedekind's lemma, distinct additive characters with values in
  a field are linearly independent; hence `AddChar.natCard_le`.
-/

@[expose] public section

namespace AddChar

variable {A R : Type*} [AddGroup A] [Fintype A] [CommRing R]

/-- If `ψ(b) - 1` is a unit for some `b`, then the sum of the values of the additive character
`ψ` vanishes: translation by `b` shows `ψ(b) ∑_a ψ(a) = ∑_a ψ(a)`. -/
theorem sum_eq_zero_of_isUnit_sub_one {ψ : AddChar A R} {b : A} (hb : IsUnit (ψ b - 1)) :
    ∑ a, ψ a = 0 := by
  have hS : ψ b * ∑ a, ψ a = ∑ a, ψ a := by
    rw [Finset.mul_sum]
    exact Fintype.sum_equiv (Equiv.addLeft b) _ _ fun a ↦ by
      rw [Equiv.coe_addLeft, map_add_eq_mul]
  exact hb.mul_left_cancel (by rw [sub_mul, hS, one_mul, sub_self, mul_zero])

section Dedekind

variable {G K : Type*} [AddMonoid G] [Field K]

/-- **Dedekind's lemma for additive characters**: distinct additive characters with values in a
field are linearly independent. -/
theorem linearIndependent_coe : LinearIndependent K ((⇑) : AddChar G K → G → K) :=
  (linearIndependent_monoidHom (Multiplicative G) K).comp
    (fun φ : AddChar G K ↦ toMonoidHomEquiv φ) toMonoidHomEquiv.injective

/-- A finite group has finitely many additive characters with values in a field. -/
instance instFinite [Finite G] : Finite (AddChar G K) :=
  have := Fintype.ofFinite G
  linearIndependent_coe.finite

/-- A finite group has at most as many additive characters with values in a field as elements. -/
theorem natCard_le [Finite G] : Nat.card (AddChar G K) ≤ Nat.card G := by
  have := Fintype.ofFinite G
  have := Fintype.ofFinite (AddChar G K)
  simpa only [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card] using
    (linearIndependent_coe (G := G) (K := K)).fintype_card_le_finrank

end Dedekind

end AddChar
