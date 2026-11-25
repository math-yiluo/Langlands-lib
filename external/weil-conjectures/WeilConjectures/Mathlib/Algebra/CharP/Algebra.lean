/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Basic

/-!
# Characteristic along a ring homomorphism

`CharP.of_ringHom_of_prime`: if a prime `p` vanishes in `R`, then every nontrivial ring `A`
receiving a ring homomorphism from `R` has characteristic `p`. Unlike
`CharP.of_ringHom_of_ne_zero`, `R` need not be a domain.
-/

@[expose] public section

variable {R A : Type*} [NonAssocSemiring R] [NonAssocSemiring A] [Nontrivial A]

/-- If a prime `p` vanishes in `R` and `f : R →+* A` is a ring homomorphism to a nontrivial
ring, then `A` has characteristic `p`. -/
theorem CharP.of_ringHom_of_prime (f : R →+* A) {p : ℕ} (hp : p.Prime) (h : (p : R) = 0) :
    CharP A p := by
  rw [CharP.charP_iff_prime_eq_zero hp, ← map_natCast f, h, map_zero]
