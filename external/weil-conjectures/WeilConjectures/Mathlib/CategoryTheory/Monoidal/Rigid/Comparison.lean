/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Monoidal functors and the dualizability criterion

For a monoidal functor `G` between monoidal closed categories, the comparison map
`[X, 𝟙] ⊗ Z ⟶ [X, Z]` (`CategoryTheory.MonoidalClosed.ihomUnitTensorToIhom`) is carried by `G`
to the comparison map of `G X` and `G Z`, up to the tensorator and the comparison maps
`G [X, -] ⟶ [G X, G -]` (`CategoryTheory.Functor.Monoidal.map_ihomUnitTensorToIhom_comp`). When
these comparison maps are isomorphisms, `G` therefore preserves and reflects the invertibility of
the comparison map, which is the criterion `CategoryTheory.MonoidalClosed.exactPairingOfIsIso`
for `[X, 𝟙]` to be a left dual of `X`.
-/

@[expose] public section

namespace CategoryTheory.Functor.Monoidal

open MonoidalCategory MonoidalClosed LaxMonoidal OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalClosed C] [MonoidalClosed D] (G : C ⥤ D) [G.Monoidal]

/-- A monoidal functor `G` carries the comparison map `[X, 𝟙] ⊗ Z ⟶ [X, Z]` to the comparison map
of `G X` and `G Z`:
```
  G ([X, 𝟙] ⊗ Z) ───── G cmp ─────▶ G [X, Z]
        │                               │
        δ                        ihomComparison
        ▼                               ▼
  G [X, 𝟙] ⊗ G Z                    [G X, G Z]
        │                               ‖
  (ihomComparison ≫ [G X, η]) ▷ G Z     ‖
        ▼                               ‖
  [G X, 𝟙] ⊗ G Z ───── cmp ──────▶ [G X, G Z]
```
-/
lemma map_ihomUnitTensorToIhom_comp (X Z : C) :
    G.map (ihomUnitTensorToIhom X Z) ≫ (ihomComparison G X).app Z =
      δ G _ Z ≫ ((ihomComparison G X).app (𝟙_ C) ≫
        (ihom (G.obj X)).map (η G)) ▷ G.obj Z ≫ ihomUnitTensorToIhom (G.obj X) (G.obj Z) := by
  apply uncurry_injective
  rw [uncurry_eq, uncurry_eq, MonoidalCategory.whiskerLeft_comp_assoc, ihomComparison_ev,
    μ_natural_right_assoc, ← G.map_comp, whiskerLeft_ihomUnitTensorToIhom_ev,
    MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerLeft_ihomUnitTensorToIhom_ev, associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight_assoc, MonoidalCategory.whiskerLeft_comp_assoc, ihom.ev_naturality,
    ihomComparison_ev_assoc]
  rw [← cancel_epi (G.obj X ◁ μ G _ Z), ← MonoidalCategory.whiskerLeft_comp_assoc, μ_δ,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]
  simp only [map_comp, map_associator_inv, map_whiskerRight, Category.assoc, μ_δ_assoc,
    comp_whiskerRight]
  simp

/-- If the comparison maps `G [X, -] ⟶ [G X, G -]` are isomorphisms, `G` carries an invertible
comparison map `[X, 𝟙] ⊗ Z ⟶ [X, Z]` to an invertible comparison map. -/
lemma isIso_ihomUnitTensorToIhom_obj (X Z : C) [IsIso (ihomComparison G X)]
    [IsIso (G.map (ihomUnitTensorToIhom X Z))] :
    IsIso (ihomUnitTensorToIhom (G.obj X) (G.obj Z)) := by
  have h := map_ihomUnitTensorToIhom_comp G X Z
  have : IsIso (δ G _ Z ≫ ((ihomComparison G X).app (𝟙_ C) ≫
      (ihom (G.obj X)).map (η G)) ▷ G.obj Z ≫ ihomUnitTensorToIhom (G.obj X) (G.obj Z)) := by
    rw [← h]; infer_instance
  have : IsIso (((ihomComparison G X).app (𝟙_ C) ≫
      (ihom (G.obj X)).map (η G)) ▷ G.obj Z ≫ ihomUnitTensorToIhom (G.obj X) (G.obj Z)) :=
    IsIso.of_isIso_comp_left (δ G _ Z) _
  exact IsIso.of_isIso_comp_left (((ihomComparison G X).app (𝟙_ C) ≫
      (ihom (G.obj X)).map (η G)) ▷ G.obj Z) _


/-- If the comparison maps `G [X, -] ⟶ [G X, G -]` are isomorphisms and the comparison map of
`G X` and `G Z` is invertible, so is the image under `G` of the comparison map of `X` and `Z`. -/
lemma isIso_map_ihomUnitTensorToIhom_of_ihomComparison (X Z : C)
    [IsIso (ihomComparison G X)]
    [IsIso (ihomUnitTensorToIhom (G.obj X) (G.obj Z))] :
    IsIso (G.map (ihomUnitTensorToIhom X Z)) := by
  have h := map_ihomUnitTensorToIhom_comp G X Z
  have : IsIso (G.map (ihomUnitTensorToIhom X Z) ≫ (ihomComparison G X).app Z) := by
    rw [h]; infer_instance
  exact IsIso.of_isIso_comp_right _ ((ihomComparison G X).app Z)

end CategoryTheory.Functor.Monoidal
