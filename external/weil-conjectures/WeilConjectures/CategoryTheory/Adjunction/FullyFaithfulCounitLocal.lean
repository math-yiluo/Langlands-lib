/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# A right adjoint is fully faithful on the objects where the counit is invertible

For an adjunction `F ⊣ G` with `G : D ⥤ C` and a fully faithful `i : A ⥤ D` such that the counit
`F (G (i X)) ⟶ i X` is invertible for every `X`, the composite `i ⋙ G` is fully faithful
(`CategoryTheory.Adjunction.fullyFaithfulOfIsIsoCounitApp`): a morphism `g : G (i X) ⟶ G (i Y)`
comes from `ε⁻¹ ≫ F g ≫ ε : i X ⟶ i Y`. This is a local form of
`CategoryTheory.Adjunction.fullyFaithfulROfIsIsoCounit`.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {A C D : Type*} [Category* A] [Category* C] [Category* D] {F : C ⥤ D} {G : D ⥤ C}
  (adj : F ⊣ G)

/-- The counit of `F ⊣ G` is invertible at `F A` as soon as the unit is invertible at `A`, by
the triangle identity. -/
lemma isIso_counit_app_obj_of_isIso_unit_app (X : C) [IsIso (adj.unit.app X)] :
    IsIso (adj.counit.app (F.obj X)) :=
  isIso_of_hom_comp_eq_id _ (adj.left_triangle_components X)

/-- The counit of `F ⊣ G` is invertible at an object isomorphic to one where it is. -/
lemma isIso_counit_app_of_iso' {X Y : D} (e : X ≅ Y) [IsIso (adj.counit.app X)] :
    IsIso (adj.counit.app Y) := by
  have h := adj.counit.naturality e.hom
  simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map] at h
  have : IsIso (F.map (G.map e.hom) ≫ adj.counit.app Y) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map (G.map e.hom)) _

/-- **A right adjoint is fully faithful on the objects where the counit is invertible.** -/
noncomputable def fullyFaithfulOfIsIsoCounitApp (i : A ⥤ D) (hi : i.FullyFaithful)
    (h : ∀ X, IsIso (adj.counit.app (i.obj X))) : (i ⋙ G).FullyFaithful where
  preimage {X Y} g := hi.preimage (inv (adj.counit.app (i.obj X)) ≫ F.map g ≫
    adj.counit.app (i.obj Y))
  map_preimage {X Y} g := by
    simp only [Functor.comp_obj, Functor.comp_map, Functor.FullyFaithful.map_preimage,
      Functor.map_comp]
    have h₁ : G.map (inv (adj.counit.app (i.obj X))) = adj.unit.app (G.obj (i.obj X)) := by
      rw [← cancel_mono (G.map (adj.counit.app (i.obj X))), ← G.map_comp, IsIso.inv_hom_id,
        G.map_id, adj.right_triangle_components]
      rfl
    have h₂ := adj.unit.naturality g
    simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at h₂
    rw [h₁, ← Category.assoc, ← h₂, Category.assoc, adj.right_triangle_components,
      Category.comp_id]
  preimage_map {X Y} f := hi.map_injective (by
    simp only [Functor.comp_obj, Functor.comp_map, Functor.FullyFaithful.map_preimage]
    have h₂ := adj.counit.naturality (i.map f)
    simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map] at h₂
    rw [h₂, IsIso.inv_hom_id_assoc])

end CategoryTheory.Adjunction
