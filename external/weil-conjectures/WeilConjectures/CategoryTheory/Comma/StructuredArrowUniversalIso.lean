/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Transport of universal arrows along isomorphisms

A universal arrow `g : X ⟶ R.obj Y` stays universal after precomposition with an isomorphism
`X' ≅ X` and postcomposition with the image of an isomorphism `Y ≅ Y'`.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.StructuredArrow

variable {C : Type*} [Category C] {D : Type*} [Category D] {R : D ⥤ C}

/-- Universal arrows are stable under precomposition with an isomorphism of sources and
postcomposition with the image of an isomorphism of targets. -/
theorem IsUniversal.nonempty_iso_comp {X X' : C} {Y Y' : D} (e : X' ≅ X)
    (g : X ⟶ R.obj Y) (e' : Y ≅ Y') (h : IsUniversal (mk g)) :
    Nonempty (IsUniversal (mk (e.hom ≫ g ≫ R.map e'.hom))) := by
  have h₁ : IsUniversal (mk (g ≫ R.map e'.hom)) :=
    h.ofIso (isoMk e' (by simp))
  have h₂ := h₁.isInitialObj (mapIso (T := R) e.symm).functor
  exact ⟨h₂.ofIso (isoMk (Iso.refl _) (by simp))⟩

end CategoryTheory.StructuredArrow
