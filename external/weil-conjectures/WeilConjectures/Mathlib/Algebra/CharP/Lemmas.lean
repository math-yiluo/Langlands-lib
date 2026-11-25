/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations

/-!
# The `p ^ n`-th power map of a ring in which a prime `p` vanishes

If `p` is a prime and `(p : R) = 0` in a commutative ring `R`, then `x ↦ x ^ p ^ n` is a ring
endomorphism of `R`. Mathlib's `iterateFrobenius` needs an `ExpChar R p` instance, which fails
for the zero ring; the version here only assumes `(p : R) = 0`, so that it applies uniformly to
all rings of sections of a scheme over `𝔽_p`, including the zero ring of sections over `∅`.

## Main definitions

- `iterateFrobeniusOfPrime`: the ring endomorphism `x ↦ x ^ p ^ n`.

## Main statements

- `exists_comp_eq_iterateFrobeniusOfPrime`: for `n ≥ 1`, the map `x ↦ x ^ p ^ n` factors through
  every surjection with square-zero kernel.
-/

@[expose] public section

/-- The `p ^ n`-th power map of a commutative ring `R` in which the prime `p` vanishes, as a ring
endomorphism. Unlike `iterateFrobenius`, no `ExpChar` instance is needed, so `R` may be the zero
ring. -/
def iterateFrobeniusOfPrime (R : Type*) [CommRing R] {p : ℕ} (hp : p.Prime) (hR : (p : R) = 0)
    (n : ℕ) : R →+* R where
  toFun x := x ^ p ^ n
  map_one' := one_pow _
  map_mul' x y := mul_pow x y _
  map_zero' := zero_pow (pow_ne_zero _ hp.ne_zero)
  map_add' x y := by
    nontriviality R
    have : Fact p.Prime := ⟨hp⟩
    have := (CharP.charP_iff_prime_eq_zero hp).2 hR
    exact add_pow_char_pow x y p n

@[simp]
lemma iterateFrobeniusOfPrime_apply (R : Type*) [CommRing R] {p : ℕ} (hp : p.Prime)
    (hR : (p : R) = 0) (n : ℕ) (x : R) : iterateFrobeniusOfPrime R hp hR n x = x ^ p ^ n :=
  rfl

/-- In a ring `R` with `p = 0`, the `p ^ n`-power map, `n ≥ 1`, factors through every surjection
`φ : R →+* S` with square-zero kernel. -/
lemma exists_comp_eq_iterateFrobeniusOfPrime {R S : Type*} [CommRing R] [CommRing S] {p : ℕ}
    (hp : p.Prime) (hR : (p : R) = 0) (φ : R →+* S) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ ^ 2 = ⊥) {n : ℕ} (hn : n ≠ 0) :
    ∃ ψ : S →+* R, ψ.comp φ = iterateFrobeniusOfPrime R hp hR n := by
  have hle : RingHom.ker φ ≤ RingHom.ker (iterateFrobeniusOfPrime R hp hR n) := by
    intro r hr
    have hr2 : r ^ 2 = 0 := by
      have : r ^ 2 ∈ RingHom.ker φ ^ 2 := Ideal.pow_mem_pow hr 2
      rwa [hker, Ideal.mem_bot] at this
    rw [RingHom.mem_ker, iterateFrobeniusOfPrime_apply]
    exact pow_eq_zero_of_le (hp.two_le.trans (Nat.le_self_pow hn p)) hr2
  exact ⟨RingHom.liftOfRightInverse φ (Function.surjInv hφ) (Function.rightInverse_surjInv hφ)
    ⟨_, hle⟩, RingHom.liftOfRightInverse_comp φ _ _ ⟨_, hle⟩⟩
