/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-!
# The inclusion of the bottom intermediate field

The inclusion of the bottom intermediate field `⊥` of `E/F` into an intermediate field `L` is,
through the identification `⊥ ≃ F` of `IntermediateField.botEquiv`, the algebra map of `L`
(`IntermediateField.inclusion_bot_apply`).
-/

@[expose] public section

namespace IntermediateField

/-- The inclusion of `⊥` into an intermediate field `L` is the algebra map `F → L`, through the
identification `IntermediateField.botEquiv : ⊥ ≃ F`. -/
lemma inclusion_bot_apply {F E : Type*} [Field F] [Field E] [Algebra F E]
    (L : IntermediateField F E) (h : ⊥ ≤ L) (x : (⊥ : IntermediateField F E)) :
    inclusion h x = algebraMap F L (botEquiv F E x) := by
  obtain ⟨r, rfl⟩ := (botEquiv F E).symm.surjective x
  rw [AlgEquiv.apply_symm_apply]
  apply Subtype.ext
  simp

end IntermediateField
