/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Localization.Bousfield

/-!
# Reflective subcategories from local units

Let `P : ObjectProperty C`, let `L : C ⥤ C` be a functor landing in `P`, and let
`η : 𝟭 C ⟶ L` be a natural transformation whose components are `P`-local. Then `L`, viewed as
a functor to the full subcategory of `P`, is left adjoint to the inclusion
(`CategoryTheory.ObjectProperty.adjunctionOfIsLocal`). This is a converse to
`CategoryTheory.ObjectProperty.isLocal_adj_unit_app`.
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category* C] (P : ObjectProperty C) {L : C ⥤ C} (hL : ∀ X, P (L.obj X))
  {η : 𝟭 C ⟶ L} (hη : ∀ X, P.isLocal (η.app X))

/-- If `L : C ⥤ C` lands in `P` and `η : 𝟭 C ⟶ L` is objectwise `P`-local, then `L`, as a
functor to the full subcategory of `P`, is left adjoint to the inclusion, with unit `η`:
every `f : X ⟶ Y` to an object `Y` satisfying `P` factors uniquely through `η.app X`.
```
X ──η.app X──▶ L X
  ╲             ┆
   f            ┆ ∃! f̃
    ╲           ▼
     ╲────────▶ Y      (P Y)
```
-/
noncomputable def adjunctionOfIsLocal : P.lift L hL ⊣ P.ι :=
  Adjunction.mkOfHomEquiv
    { homEquiv X Y := (P.fullyFaithfulι.homEquiv (X := (P.lift L hL).obj X) (Y := Y)).trans
        ((hη X).homEquiv (P.ι.obj Y) Y.property)
      homEquiv_naturality_left_symm {X X'} Y f g := by
        rw [Equiv.symm_apply_eq]
        simp only [Equiv.trans_apply, Equiv.symm_trans_apply, Functor.FullyFaithful.homEquiv,
          Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, ι_map, lift_map, FullSubcategory.comp_hom,
          homMk_hom]
        change f ≫ g = η.app X ≫ L.map f ≫ _
        rw [← η.naturality_assoc]
        exact congrArg (f ≫ ·) (((hη X').homEquiv _ Y.property).apply_symm_apply g).symm
      homEquiv_naturality_right f g := (Category.assoc _ _ _).symm }

@[simp]
lemma adjunctionOfIsLocal_unit_app (X : C) :
    (P.adjunctionOfIsLocal hL hη).unit.app X = η.app X := by
  change η.app X ≫ 𝟙 _ = _
  exact Category.comp_id _

end CategoryTheory.ObjectProperty
