/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Opposites

/-!
# Type-valued presheaves

Two composites of morphisms which agree induce the same map on sections of a presheaf of types
(`CategoryTheory.FunctorToTypes.map_map_eq_map_map_of_comp_eq`).
-/

@[expose] public section

namespace CategoryTheory.FunctorToTypes

/-- Two composites of morphisms which agree induce the same map on sections of a presheaf. -/
lemma map_map_eq_map_map_of_comp_eq {D : Type*} [Category D] (P : Dᵒᵖ ⥤ Type*)
    {A B B' E : D} (u : A ⟶ B) (v : B ⟶ E) (u' : A ⟶ B') (v' : B' ⟶ E) (h : u ≫ v = u' ≫ v')
    (x : P.obj (.op E)) : P.map u.op (P.map v.op x) = P.map u'.op (P.map v'.op x) := by
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, h]

end CategoryTheory.FunctorToTypes
