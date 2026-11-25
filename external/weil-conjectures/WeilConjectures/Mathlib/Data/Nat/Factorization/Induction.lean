/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Nat.Factorization.Induction

/-!
# Invertibility of a natural number from its prime factors

A positive integer all of whose prime factors are invertible in a commutative ring is invertible
there.
-/

@[expose] public section

/-- A positive integer all of whose prime factors are invertible in a commutative ring is
invertible. -/
lemma isUnit_natCast_of_forall_mem_primeFactors {R : Type*} [CommRing R] :
    ∀ (n : ℕ), 0 < n → (∀ p ∈ n.primeFactors, IsUnit (p : R)) → IsUnit (n : R) := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | one => intros; simp
  | prime_pow p k hp hk =>
    intro _ h
    have := h p (by simp [Nat.primeFactors_prime_pow hk.ne' hp])
    simpa using this.pow k
  | coprime a b ha hb hab iha ihb =>
    intro hn h
    rw [Nat.cast_mul]
    refine (iha (by lia) fun q hq ↦ h q ?_).mul (ihb (by lia) fun q hq ↦ h q ?_)
    · exact Nat.primeFactors_mono (Dvd.intro b rfl) (by lia) hq
    · exact Nat.primeFactors_mono (Dvd.intro_left a rfl) (by lia) hq
