/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # Maps from reduced schemes through closed subschemes

## References

* Stacks Project, Schemes, Lemma 0356, lines 2268-2289
-/

@[expose] public section

universe u

open CategoryTheory
namespace AlgebraicGeometry

/-- A morphism from a reduced scheme factors through a closed subscheme exactly
set-theoretically; every map factors through the reduction.
-/
theorem reduced_source_factors_through_closed_subscheme
    {X Y Z : Scheme.{u}} [IsReduced Y]
    (i : Z ⟶ X) [IsClosedImmersion i] (f : Y ⟶ X) :
    ((∃ g : Y ⟶ Z, g ≫ i = f) ↔ Set.range f.base ⊆ Set.range i.base) ∧
      (∃ g : Y ⟶ X.nilradical.subscheme, g ≫ X.nilradical.subschemeι = f) := by
  constructor
  · constructor
    · rintro ⟨g, rfl⟩ y ⟨x, rfl⟩
      exact ⟨g.base x, rfl⟩
    · intro h
      exact (IsClosedImmersion.existsUnique_fac_of_range_subset_range i f h).exists
  · exact ⟨f.liftNilradical, f.liftNilradical_subschemeι⟩

end AlgebraicGeometry
