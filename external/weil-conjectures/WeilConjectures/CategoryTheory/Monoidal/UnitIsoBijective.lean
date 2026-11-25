/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Whiskering with an object isomorphic to the unit

In a monoidal category, whiskering with an object `B ≅ 𝟙_` is a bijection on morphisms. This is
used to eliminate Tate twists over a separably closed field, where the twisting objects are
isomorphic to the unit.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category C]

/-- Composing on both sides with isomorphisms is a bijection on morphisms. -/
lemma _root_.CategoryTheory.bijective_conj {W W' Z Z' : C} (e : W ≅ W') (f : Z ≅ Z') :
    Function.Bijective (fun z : W' ⟶ Z ↦ e.hom ≫ z ≫ f.hom) :=
  ⟨fun a b hab ↦ by simpa using congrArg (fun z ↦ e.inv ≫ z ≫ f.inv) hab,
    fun z ↦ ⟨e.inv ≫ z ≫ f.inv, by simp⟩⟩

/-- Precomposition with an isomorphism transports bijectivity of a postcomposition map:
if `y ↦ y ≫ t` is bijective on morphisms out of `W'`, then so it is on morphisms out of
`W ≅ W'`. -/
lemma _root_.CategoryTheory.bijective_comp_of_iso_left {W W' N P : C} (e : W ≅ W') (t : N ⟶ P)
    (h : Function.Bijective (fun y : W' ⟶ N ↦ y ≫ t)) :
    Function.Bijective (fun y : W ⟶ N ↦ y ≫ t) := by
  have : (fun y : W ⟶ N ↦ y ≫ t) = (fun z : W' ⟶ P ↦ e.hom ≫ z ≫ (Iso.refl P).hom) ∘
      (fun y : W' ⟶ N ↦ y ≫ t) ∘ (fun y : W ⟶ N ↦ e.symm.hom ≫ y ≫ (Iso.refl N).hom) := by
    funext y
    simp
  rw [this]
  exact (bijective_conj e (Iso.refl P)).comp (h.comp (bijective_conj e.symm (Iso.refl N)))

variable [MonoidalCategory C]

/-- Whiskering on the right with an object isomorphic to the unit is a bijection on morphisms:
`g ▷ B` is `g` conjugated by the isomorphisms `X ⊗ B ≅ X ⊗ 𝟙_ ≅ X`. -/
lemma bijective_whiskerRight_of_iso_unit {B : C} (e : B ≅ 𝟙_ C) (X Y : C) :
    Function.Bijective (fun g : X ⟶ Y ↦ g ▷ B) := by
  let E (Z : C) : Z ⊗ B ≅ Z := whiskerLeftIso Z e ≪≫ ρ_ Z
  have h (g : X ⟶ Y) : g ▷ B = (E X).hom ≫ g ≫ (E Y).symm.hom := by
    simp only [E, Iso.symm_hom, Iso.trans_hom, Iso.trans_inv, whiskerLeftIso_hom,
      whiskerLeftIso_inv, Category.assoc]
    rw [← rightUnitor_naturality_assoc, Iso.hom_inv_id_assoc, whisker_exchange_assoc,
      ← MonoidalCategory.whiskerLeft_comp, e.hom_inv_id, MonoidalCategory.whiskerLeft_id,
      Category.comp_id]
  have : (fun g : X ⟶ Y ↦ g ▷ B) = fun g ↦ (E X).hom ≫ g ≫ (E Y).symm.hom := funext h
  rw [this]
  exact bijective_conj (E X) (E Y).symm

/-- **Elimination of a twist isomorphic to the unit.** Let `c : 𝟙_ ≅ A ⊗ B` with `A ≅ 𝟙_` and
`B ≅ 𝟙_`, and let `T : M ⊗ A ⟶ 𝟙_` factor as an isomorphism `θ : M ⊗ A ≅ N` followed by
`t : N ⟶ 𝟙_`. If `y ↦ y ≫ t` is a bijection `Hom(𝟙_, N) ≃ Hom(𝟙_, 𝟙_)`, then `x ↦ x ≫ τ` is a
bijection `Hom(𝟙_, M) ≃ Hom(𝟙_, B)` for the untwisted map
```
       ρ⁻¹            M ◁ c          α⁻¹                   T ▷ B             λ
τ : M ─────▶ M ⊗ 𝟙_ ─────▶ M ⊗ (A ⊗ B) ────▶ (M ⊗ A) ⊗ B ────────▶ 𝟙_ ⊗ B ────▶ B.
``` -/
lemma bijective_comp_untwist {M A B N : C} (c : 𝟙_ C ≅ A ⊗ B) (eA : A ≅ 𝟙_ C)
    (eB : B ≅ 𝟙_ C) (θ : M ⊗ A ⟶ N) [IsIso θ] (t : N ⟶ 𝟙_ C)
    (h : Function.Bijective (fun y : 𝟙_ C ⟶ N ↦ y ≫ t)) :
    Function.Bijective (fun x : 𝟙_ C ⟶ M ↦ x ≫ (ρ_ M).inv ≫ M ◁ c.hom ≫ (α_ M A B).inv ≫
      (θ ≫ t) ▷ B ≫ (λ_ B).hom) := by
  let E : 𝟙_ C ≅ (𝟙_ C ⊗ A) ⊗ B :=
    (ρ_ (𝟙_ C)).symm ≪≫ whiskerLeftIso (𝟙_ C) c ≪≫ (α_ (𝟙_ C) A B).symm
  have : (fun x : 𝟙_ C ⟶ M ↦ x ≫ (ρ_ M).inv ≫ M ◁ c.hom ≫ (α_ M A B).inv ≫
      (θ ≫ t) ▷ B ≫ (λ_ B).hom) =
      (fun z : (𝟙_ C ⊗ A) ⊗ B ⟶ 𝟙_ C ⊗ B ↦ E.hom ≫ z ≫ (λ_ B).hom) ∘
      (fun g : 𝟙_ C ⊗ A ⟶ 𝟙_ C ↦ g ▷ B) ∘ (fun y : 𝟙_ C ⊗ A ⟶ N ↦ y ≫ t) ∘
      (fun z : 𝟙_ C ⊗ A ⟶ M ⊗ A ↦ (Iso.refl _).hom ≫ z ≫ (asIso θ).hom) ∘
      (fun x : 𝟙_ C ⟶ M ↦ x ▷ A) := by
    funext x
    simp only [E, Function.comp_apply, comp_whiskerRight, Category.assoc, Iso.trans_hom,
      Iso.symm_hom, whiskerLeftIso_hom, Iso.refl_hom, asIso_hom, Category.id_comp]
    rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
      associator_inv_naturality_left_assoc]
  rw [this]
  exact (bijective_conj E (λ_ B)).comp ((bijective_whiskerRight_of_iso_unit eB _ _).comp
    ((bijective_comp_of_iso_left (whiskerLeftIso (𝟙_ C) eA ≪≫ ρ_ _) t h).comp
      ((bijective_conj (Iso.refl _) (asIso θ)).comp (bijective_whiskerRight_of_iso_unit eA _ _))))

end CategoryTheory.MonoidalCategory
