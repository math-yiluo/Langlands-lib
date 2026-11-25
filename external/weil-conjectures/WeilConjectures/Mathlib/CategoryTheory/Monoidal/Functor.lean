/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Category

/-!
# Transport of a lax monoidal structure along a natural isomorphism

`CategoryTheory.Functor.Monoidal.transport` transports a strong monoidal structure along a
natural isomorphism of functors. Here we do the same for lax monoidal structures.

We also show that the right adjoint `G` of a monoidal adjunction `F ⊣ G` whose unit and counit
are isomorphisms (i.e. an adjoint equivalence) is strong monoidal as soon as `F` is: the lax
structure of `G` is determined by the oplax structure of `F` and the adjunction.

## Main definitions and results

- `CategoryTheory.Functor.LaxMonoidal.transport`: the lax monoidal structure on a functor
  that is isomorphic to a lax monoidal functor.
- `CategoryTheory.Adjunction.isIso_ε_of_isIso_η` and
  `CategoryTheory.Adjunction.isIso_μ_of_isIso_δ`: for a monoidal adjunction `F ⊣ G` with
  invertible unit and counit, the comparison maps of `G` are invertible if those of `F` are.
- `CategoryTheory.Functor.eq_of_leftUnitality`: the unit comparison `F (𝟙_ D) ⟶ 𝟙_ C` of a
  functor is determined by an invertible tensor comparison and the left unitality axiom.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.LaxMonoidal

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- Transport a lax monoidal structure along a natural isomorphism of functors. -/
@[instance_reducible]
def transport {F G : C ⥤ D} [F.LaxMonoidal] (i : F ≅ G) : G.LaxMonoidal where
  ε := ε F ≫ i.hom.app _
  μ X Y := (i.inv.app X ⊗ₘ i.inv.app Y) ≫ μ F X Y ≫ i.hom.app (X ⊗ Y)
  μ_natural_left f X' := by
    simp only [Category.assoc, NatTrans.whiskerRight_app_tensor_app_assoc i.inv i.inv,
      μ_natural_left_assoc, ← i.hom.naturality]
  μ_natural_right X' f := by
    simp only [Category.assoc, NatTrans.whiskerLeft_app_tensor_app_assoc i.inv i.inv,
      μ_natural_right_assoc, ← i.hom.naturality]
  associativity X Y Z := by
    rw [comp_whiskerRight, comp_whiskerRight, MonoidalCategory.whiskerLeft_comp,
      MonoidalCategory.whiskerLeft_comp, ← tensorHom_id (i.hom.app (X ⊗ Y)),
      ← id_tensorHom (G.obj X) (i.hom.app (Y ⊗ Z))]
    simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_app,
      Category.id_comp]
    rw [id_tensorHom, tensorHom_id, ← whisker_exchange_assoc (μ F X Y) (i.inv.app Z),
      whisker_exchange_assoc (i.inv.app X) (μ F Y Z), ← tensorHom_def_assoc,
      whisker_exchange_assoc (i.inv.app X) (i.inv.app Y ⊗ₘ i.inv.app Z),
      ← tensorHom_def_assoc, ← i.hom.naturality, associativity_assoc,
      associator_naturality_assoc]
  left_unitality X := by
    rw [comp_whiskerRight, ← tensorHom_id (i.hom.app (𝟙_ C)), Category.assoc, Category.assoc,
      tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_app, Category.id_comp, id_tensorHom,
      ← whisker_exchange_assoc, Category.assoc, ← i.hom.naturality, ← left_unitality_assoc]
    simp
  right_unitality X := by
    rw [MonoidalCategory.whiskerLeft_comp, ← id_tensorHom (G.obj X) (i.hom.app (𝟙_ C)),
      Category.assoc, Category.assoc, tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_app,
      Category.id_comp, tensorHom_id, whisker_exchange_assoc, Category.assoc, ← i.hom.naturality,
      ← right_unitality_assoc]
    simp

@[reassoc]
lemma transport_ε {F G : C ⥤ D} [F.LaxMonoidal] (i : F ≅ G) :
    letI := transport i
    ε G = ε F ≫ i.hom.app (𝟙_ C) :=
  rfl

@[reassoc]
lemma transport_μ {F G : C ⥤ D} [F.LaxMonoidal] (i : F ≅ G) (X Y : C) :
    letI := transport i
    μ G X Y = (i.inv.app X ⊗ₘ i.inv.app Y) ≫ μ F X Y ≫ i.hom.app (X ⊗ Y) :=
  rfl

variable (F : C ⥤ D) [F.LaxMonoidal] [IsIso (ε F)]

/-- If the unit comparison `ε` of a lax monoidal functor is an isomorphism, so is
`μ : F X ⊗ F 𝟙_ ⟶ F (X ⊗ 𝟙_)`: by right unitality, it is
`(F X ◁ ε)⁻¹ ≫ ρ_ ≫ F (ρ_)⁻¹`. -/
lemma isIso_μ_tensorUnit_right (X : C) : IsIso (μ F X (𝟙_ C)) := by
  have h : μ F X (𝟙_ C) =
      CategoryTheory.inv (F.obj X ◁ ε F) ≫ (ρ_ (F.obj X)).hom ≫ F.map (ρ_ X).inv := by
    rw [right_unitality, Category.assoc, Category.assoc, ← F.map_comp, Iso.hom_inv_id,
      F.map_id, Category.comp_id, IsIso.inv_hom_id_assoc]
  rw [h]
  infer_instance

/-- If the unit comparison `ε` of a lax monoidal functor is an isomorphism, so is
`μ : F 𝟙_ ⊗ F X ⟶ F (𝟙_ ⊗ X)`: by left unitality, it is
`(ε ▷ F X)⁻¹ ≫ λ_ ≫ F (λ_)⁻¹`. -/
lemma isIso_μ_tensorUnit_left (X : C) : IsIso (μ F (𝟙_ C) X) := by
  have h : μ F (𝟙_ C) X =
      CategoryTheory.inv (ε F ▷ F.obj X) ≫ (λ_ (F.obj X)).hom ≫ F.map (λ_ X).inv := by
    rw [left_unitality, Category.assoc, Category.assoc, ← F.map_comp, Iso.hom_inv_id,
      F.map_id, Category.comp_id, IsIso.inv_hom_id_assoc]
  rw [h]
  infer_instance

end CategoryTheory.Functor.LaxMonoidal

namespace CategoryTheory.Adjunction

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {F : C ⥤ D} {G : D ⥤ C} [F.OplaxMonoidal] [G.LaxMonoidal] (adj : F ⊣ G) [adj.IsMonoidal]

/-- For a monoidal adjunction `F ⊣ G` with invertible unit, the unit comparison map
`ε : 𝟙 ⟶ G 𝟙` is invertible if `η : F 𝟙 ⟶ 𝟙` is: it is the composite
`𝟙 ⟶ G (F 𝟙) ⟶ G 𝟙` of the unit of the adjunction and `G η`. -/
lemma isIso_ε_of_isIso_η [IsIso adj.unit] [IsIso (η F)] : IsIso (ε G) := by
  rw [IsMonoidal.leftAdjoint_ε (adj := adj)]
  infer_instance

/-- For a monoidal adjunction `F ⊣ G` with invertible unit and counit, the tensor comparison
map `μ : G X ⊗ G Y ⟶ G (X ⊗ Y)` is invertible if `δ : F (G X ⊗ G Y) ⟶ F (G X) ⊗ F (G Y)` is:
it is the composite
```
  G X ⊗ G Y ──unit──▶ G (F (G X ⊗ G Y)) ──G δ──▶ G (F (G X) ⊗ F (G Y))
            ──G (counit ⊗ counit)──▶ G (X ⊗ Y)
```
-/
lemma isIso_μ_of_isIso_δ [IsIso adj.unit] [IsIso adj.counit] (X Y : D)
    [IsIso (δ F (G.obj X) (G.obj Y))] : IsIso (μ G X Y) := by
  rw [IsMonoidal.leftAdjoint_μ (adj := adj)]
  infer_instance

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] {F : D ⥤ C}

/-- The unit comparison of a functor is determined by its tensor comparison: if
`u, u' : F (𝟙_ D) ⟶ 𝟙_ C` both satisfy the left unitality axiom of an oplax monoidal functor
for the same invertible comparison `φ : F (𝟙_ D ⊗ 𝟙_ D) ⟶ F (𝟙_ D) ⊗ F (𝟙_ D)`, and `u` is an
isomorphism, then `u = u'`. -/
lemma eq_of_leftUnitality (φ : F.obj (𝟙_ D ⊗ 𝟙_ D) ⟶ F.obj (𝟙_ D) ⊗ F.obj (𝟙_ D)) [IsIso φ]
    (u u' : F.obj (𝟙_ D) ⟶ 𝟙_ C) [IsIso u]
    (h : φ ≫ u ▷ F.obj (𝟙_ D) ≫ (λ_ _).hom = F.map (λ_ (𝟙_ D)).hom)
    (h' : φ ≫ u' ▷ F.obj (𝟙_ D) ≫ (λ_ _).hom = F.map (λ_ (𝟙_ D)).hom) :
    u = u' := by
  refine whiskerRight_injective_of_tensorIso (Y := 𝟙_ C) (ρ_ _ ≪≫ asIso u) ?_
  rw [← cancel_epi φ, ← cancel_mono (λ_ _).hom, Category.assoc, Category.assoc, h, h']

end CategoryTheory.Functor
