/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Homomorphisms between groups of prime order

A nonzero homomorphism between two additive groups of the same prime order is bijective.
-/

@[expose] public section

namespace AddMonoidHom

variable {A B : Type*} [AddGroup A] [AddGroup B]

/-- A nonzero homomorphism between additive groups of the same prime order `p` is bijective. -/
theorem bijective_of_card_eq_prime {p : ℕ} [hp : Fact p.Prime] (hA : Nat.card A = p)
    (hB : Nat.card B = p) (f : A →+ B) (hf : f ≠ 0) : Function.Bijective f := by
  have : Finite B := Nat.finite_of_card_ne_zero (by rw [hB]; exact hp.out.ne_zero)
  have : Fact (Nat.card A).Prime := hA ▸ hp
  have hinj : Function.Injective f := by
    rw [← ker_eq_bot_iff]
    rcases f.ker.eq_bot_or_eq_top_of_prime_card with h | h
    · exact h
    · exact absurd (ext fun a ↦ (mem_ker.1 (h ▸ AddSubgroup.mem_top a))) hf
  exact hinj.bijective_of_nat_card_le (by omega)

end AddMonoidHom
