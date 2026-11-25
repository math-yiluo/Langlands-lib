/-
Copyright (c) 2026 Anthropic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-!
# Morphisms into a mapping cocone

A morphism into a degree of the mapping cocone of a morphism of cochain complexes is
determined by its two coordinates (`CochainComplex.mappingCocone.ext_to`).
-/

@[expose] public section

namespace CochainComplex.mappingCocone

open CategoryTheory

/-- Morphisms into a mapping cocone are determined by their two coordinates. -/
theorem ext_to {C : Type*} [Category C] [Abelian C] {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    {T : C} (k q : ℤ) (hkq : k + -1 = q) {u v : T ⟶ (mappingCocone φ).X k}
    (h₁ : u ≫ (fst φ).f k = v ≫ (fst φ).f k)
    (h₂ : u ≫ (snd φ).v k q hkq = v ≫ (snd φ).v k q hkq) : u = v := by
  rw [← Category.comp_id u, ← Category.comp_id v, ← id_X φ k q hkq]
  simp only [Preadditive.comp_add, ← Category.assoc, h₁, h₂]

end CochainComplex.mappingCocone
