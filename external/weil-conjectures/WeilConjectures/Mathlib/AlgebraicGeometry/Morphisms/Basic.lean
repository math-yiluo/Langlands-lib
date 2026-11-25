/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-!
# Properties local at the source, checked on open immersions

A property `P` of morphisms which is local at the source holds for `f : X ⟶ Y` as soon as every
point of `X` lies in the image of an open immersion `g : U ⟶ X` with `P (g ≫ f)`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsZariskiLocalAtSource

variable {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtSource P] {X Y : Scheme.{u}}

/-- A property local at the source holds for `f : X ⟶ Y` if every point of `X` lies in the image
of an open immersion `g : U ⟶ X` such that `g ≫ f` has the property. -/
lemma of_forall_exists_isOpenImmersion (f : X ⟶ Y)
    (H : ∀ x : X, ∃ (U : Scheme.{u}) (g : U ⟶ X), IsOpenImmersion g ∧ x ∈ Set.range g.base ∧
      P (g ≫ f)) : P f := by
  choose U g hg hx hP using H
  refine of_iSup_eq_top (fun x ↦ (g x).opensRange) ?_ fun x ↦ ?_
  · refine eq_top_iff.2 fun x _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨x, ?_⟩
    simpa using hx x
  · have := hg x
    rw [← (g x).isoOpensRange_inv_comp, Category.assoc,
      MorphismProperty.cancel_left_of_respectsIso (P := P)]
    exact hP x

end AlgebraicGeometry.IsZariskiLocalAtSource
