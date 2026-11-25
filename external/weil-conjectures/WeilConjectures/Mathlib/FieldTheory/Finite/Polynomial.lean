/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Finite.Polynomial

/-!
# Frobenius on multivariate polynomials over a finite field

Over a finite field `K` with `q` elements, raising a multivariate polynomial to the `q`-th
power substitutes `Xᵢ ^ q` for each variable: `expand q f = f ^ q`. This is the multivariate
analogue of `FiniteField.expand_card`, and generalises `MvPolynomial.expand_zmod` from
`ZMod p` to an arbitrary finite field.
-/

@[expose] public section

namespace MvPolynomial

variable {σ K : Type*} [Field K] [Fintype K]

/-- Over a finite field `K` with `q` elements, `expand q f = f ^ q`. -/
theorem expand_card (f : MvPolynomial σ K) : expand (Fintype.card K) f = f ^ Fintype.card K := by
  obtain ⟨p, hp⟩ := CharP.exists K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K p
  have : Fact p.Prime := ⟨hp⟩
  rw [hn, ← iterateFrobenius_def (R := MvPolynomial σ K) p n]
  refine congrArg (· f) (ringHom_ext (fun a ↦ ?_) fun i ↦ ?_ :
    (expand (p ^ (n : ℕ)) : MvPolynomial σ K →ₐ[K] _).toRingHom = iterateFrobenius _ p n)
  · simp [iterateFrobenius_def, ← C_pow, ← hn, FiniteField.pow_card]
  · simp [iterateFrobenius_def]

/-- Over a finite field `K` with `q = Nat.card K` elements, `expand q f = f ^ q`. -/
theorem expand_natCard {K : Type*} [Field K] [Finite K] (f : MvPolynomial σ K) :
    expand (Nat.card K) f = f ^ Nat.card K := by
  have := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact expand_card f

end MvPolynomial
