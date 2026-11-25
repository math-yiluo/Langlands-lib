/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Simple

/-!
# A criterion for simple objects

A nonzero object all of whose monomorphisms are zero or isomorphisms is simple.
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C] [HasZeroMorphisms C]

/-- A nonzero object `P` is simple as soon as every monomorphism into `P` is zero or an
isomorphism. -/
theorem simple_of_forall_mono {P : C} (hP : ¬ IsZero P)
    (h : ∀ {Q : C} (f : Q ⟶ P) [Mono f], f = 0 ∨ IsIso f) : Simple P where
  mono_isIso_iff_nonzero {Q} f _ := by
    refine ⟨fun hf h0 ↦ hP ((IsZero.of_mono_eq_zero f h0).of_iso (asIso f).symm), fun hne ↦ ?_⟩
    exact (h f).resolve_left hne

end CategoryTheory
