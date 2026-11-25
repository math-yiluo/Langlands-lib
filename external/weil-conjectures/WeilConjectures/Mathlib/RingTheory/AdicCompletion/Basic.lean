/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Adically complete rings and their towers of quotients

For an ideal `I` of a commutative ring `R`, the quotient maps `R ⟶ R ⧸ Iⁿ⁺¹` exhibit an
`I`-adically complete ring as the limit of the tower of its quotients: compatible families of
residues lift (`IsPrecomplete.exists_mk_eq_of_factor_eq`), uniquely
(`IsHausdorff.eq_zero_of_forall_mk_eq_zero`).
-/

@[expose] public section

variable {R : Type*} [CommRing R] {I : Ideal R}

lemma Ideal.pow_smul_top_eq (I : Ideal R) (n : ℕ) : I ^ n • (⊤ : Submodule R R) = I ^ n := by
  rw [smul_eq_mul, Ideal.mul_top]

/-- In an `I`-adically precomplete ring, a compatible family of residues modulo the powers
`Iⁿ⁺¹` is the family of residues of a single element. -/
lemma IsPrecomplete.exists_mk_eq_of_factor_eq [IsPrecomplete I R] (x : ∀ n : ℕ, R ⧸ I ^ (n + 1))
    (hx : ∀ n, Ideal.Quotient.factor (Ideal.pow_le_pow_right (n + 1).le_succ) (x (n + 1)) = x n) :
    ∃ r : R, ∀ n, Ideal.Quotient.mk (I ^ (n + 1)) r = x n := by
  choose f hf using fun n ↦ Ideal.Quotient.mk_surjective (x n)
  have key (n : ℕ) :
      Ideal.Quotient.mk (I ^ (n + 1)) (f (n + 1)) = Ideal.Quotient.mk (I ^ (n + 1)) (f n) := by
    rw [hf n, ← hx n, ← hf (n + 1), Ideal.Quotient.factor_mk]
  have hmn : ∀ {m n : ℕ}, m ≤ n → Ideal.Quotient.mk (I ^ (m + 1)) (f n) = x m := by
    intro m n h
    induction h with
    | refl => exact hf m
    | @step n h ih =>
      rw [← ih, Ideal.Quotient.eq]
      exact Ideal.pow_le_pow_right (Nat.succ_le_succ h) (Ideal.Quotient.eq.1 (key n))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := R) ‹_› (f := f) (by
    intro m n h
    rw [SModEq.sub_mem, Ideal.pow_smul_top_eq]
    rcases m with _ | m
    · simp
    rw [← Ideal.Quotient.eq, hmn (Nat.le_succ m), hmn (Nat.le_of_succ_le h)])
  refine ⟨L, fun n ↦ ?_⟩
  have := hL (n + 1)
  rw [SModEq.sub_mem, Ideal.pow_smul_top_eq, ← Ideal.Quotient.eq] at this
  rw [← this, hmn (Nat.le_succ n)]

/-- In an `I`-adically Hausdorff ring, an element whose residues modulo all powers `Iⁿ⁺¹`
vanish is zero. -/
lemma IsHausdorff.eq_zero_of_forall_mk_eq_zero [IsHausdorff I R] (r : R)
    (h : ∀ n, Ideal.Quotient.mk (I ^ (n + 1)) r = 0) : r = 0 := by
  refine IsHausdorff.haus ‹_› r fun n ↦ ?_
  rw [SModEq.sub_mem, Ideal.pow_smul_top_eq, sub_zero]
  rcases n with _ | n
  · simp
  rw [← Ideal.Quotient.eq_zero_iff_mem, h]
