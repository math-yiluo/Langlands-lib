/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Generator.StrongGenerator

/-!
# Separating families in balanced categories are strong generators

## Main results

- `ObjectProperty.IsSeparating.isStrongGenerator`: in a balanced category, a separating
  family is a strong generator.
- `IsSeparator.isStrongGenerator`: in a balanced category, a separator is a strong generator.
-/

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Balanced C]

/-- In a balanced category, a separating family of objects is a strong generator. -/
lemma ObjectProperty.IsSeparating.isStrongGenerator {P : ObjectProperty C}
    (hP : P.IsSeparating) : P.IsStrongGenerator := by
  refine isStrongGenerator_iff.2 ⟨hP, fun X Y i _ hi ↦ ?_⟩
  have : Epi i := ⟨fun u v huv ↦ hP _ _ fun G hG g ↦ by
    obtain ⟨f, rfl⟩ := hi G hG g
    simp [huv]⟩
  exact isIso_of_mono_of_epi i

/-- In a balanced category, a separator is a strong generator. -/
lemma IsSeparator.isStrongGenerator {G : C} (hG : IsSeparator G) :
    (ObjectProperty.singleton G).IsStrongGenerator :=
  ObjectProperty.IsSeparating.isStrongGenerator hG

end CategoryTheory
