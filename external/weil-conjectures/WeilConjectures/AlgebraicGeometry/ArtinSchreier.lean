/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import WeilConjectures.Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Artin–Schreier map over an algebraically closed field

Source: blueprint sec-abelian-varieties/lem-sc-lang-steinberg/lem-sc-artin-schreier-k.md
(blueprint: proposition-p-torsion-smooth-proper-curve--2)
-/

@[expose] public section

namespace IsAlgClosed

/-- Artin–Schreier on an algebraically closed field.

Source: blueprint sec-abelian-varieties/lem-sc-lang-steinberg/lem-sc-artin-schreier-k.md,
Proof; Stacks Project, Tag 0A3J, opening Artin–Schreier sequence
(blueprint: proposition-p-torsion-smooth-proper-curve--2).

Proof:
1. Positive field characteristic is prime: if `p = m * n` with both factors strictly between
   `1` and `p`, their nonzero casts would multiply to zero in the field
   (`def-pc-field-characteristic`). In particular `p ≥ 2`. Given `a : k`, the polynomial
   `X ^ p - X - a` has degree `p`, hence is nonconstant. Algebraic closedness gives a root
   (`def-weil-algebraic-closure`), which satisfies `x ^ p - x = a`, proving surjectivity.
2. The equation `x ^ p - x = 0` is equivalent to `x ^ p = x`. The field kernel result
   (`lem-sc-field-artin-schreier-kernel`) identifies these elements with the prime subfield:
   use `Subfield.mem_bot_iff_pow_eq_self`, then `ZMod.fieldRange_castHom_eq_bot` to identify
   that subfield with the range of the canonical `ZMod p` embedding. This is the stated
   kernel `𝔽_p`.
-/
theorem artinSchreier_surjective_and_kernel {k : Type*} [Field k] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    Function.Surjective (fun x : k => x ^ p - x) ∧
      {x : k | x ^ p - x = 0} = Set.range (ZMod.castHom (dvd_refl p) k) := by
  constructor
  · exact surjective_pow_sub_self p
  · ext x
    change (x ^ p - x = 0) ↔ x ∈ Set.range (ZMod.castHom (dvd_refl p) k)
    rw [Set.mem_range]
    constructor
    · intro hx
      have hbot : x ∈ (⊥ : Subfield k) :=
        (Subfield.mem_bot_iff_pow_eq_self (F := k) p).mpr (sub_eq_zero.mp hx)
      have hrange : x ∈ (ZMod.castHom (dvd_refl p) k).fieldRange := by
        rw [ZMod.fieldRange_castHom_eq_bot p]
        exact hbot
      exact RingHom.mem_fieldRange.mp hrange
    · rintro ⟨z, rfl⟩
      simp only [sub_eq_zero]
      exact (Subfield.mem_bot_iff_pow_eq_self (F := k) p).mp (by
        rw [← ZMod.fieldRange_castHom_eq_bot p]
        exact RingHom.mem_fieldRange.mpr ⟨z, rfl⟩)

end IsAlgClosed
