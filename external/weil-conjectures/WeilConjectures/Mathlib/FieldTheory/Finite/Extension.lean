/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Subextensions of every degree of an algebraically closed extension of a finite field

## Main statements

- `FiniteField.exists_intermediateField_finrank_eq`: an algebraically closed extension of a
  finite field `k` contains an intermediate field of every positive degree over `k`.
-/

@[expose] public section

namespace FiniteField

/-- An algebraically closed extension of a finite field `k` contains an intermediate field of any
given positive degree over `k`. -/
theorem exists_intermediateField_finrank_eq (k K : Type*) [Field k] [Finite k] [Field K]
    [Algebra k K] [IsAlgClosed K] {M : ℕ} (hM : 0 < M) :
    ∃ F : IntermediateField k K, Module.finrank k F = M := by
  have : NeZero M := ⟨hM.ne'⟩
  obtain ⟨p, hp⟩ := CharP.exists k
  have : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  let ε : Extension k p M →ₐ[k] K := IsAlgClosed.lift
  refine ⟨ε.fieldRange, ?_⟩
  rw [← ε.equivFieldRange.toLinearEquiv.finrank_eq, finrank_extension]

end FiniteField
