/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor

/-! # A unit comparison for an invertible associative tensor comparison

A tensor comparison preserving associativity admits a compatible left unit whenever
its image of the unit is isomorphic to the target unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace CategoryTheory

private theorem action_unit {D : Type*} [Category D] [MonoidalCategory D]
    {O Y : D} (m : O ⊗ O ≅ O) (a : O ⊗ Y ≅ Y) (ε : O ≅ 𝟙_ D)
    (hm : m.hom = ε.hom ▷ O ≫ (λ_ O).hom)
    (ha : m.hom ▷ Y ≫ a.hom =
      (α_ O O Y).hom ≫ O ◁ a.hom ≫ a.hom) :
    a.hom = ε.hom ▷ Y ≫ (λ_ Y).hom := by
  apply (cancel_epi (O ◁ a.hom)).mp
  have h : m.hom ▷ Y = (α_ O O Y).hom ≫ O ◁ a.hom :=
    (cancel_mono a.hom).mp (by simpa only [Category.assoc] using ha)
  rw [hm, comp_whiskerRight, leftUnitor_whiskerRight,
    associator_naturality_left_assoc] at h
  have h' := (cancel_epi (α_ O O Y).hom).mp h
  calc
    _ = (ε.hom ▷ (O ⊗ Y)) ≫ (λ_ (O ⊗ Y)).hom ≫ a.hom := by
      rw [← h', Category.assoc]
    _ = (ε.hom ▷ (O ⊗ Y)) ≫ 𝟙_ D ◁ a.hom ≫ (λ_ Y).hom := by
      rw [leftUnitor_naturality]
    _ = _ := by rw [whisker_exchange_assoc]

/-- An associative invertible tensor comparison has a compatible left-unit map
if the image of the source unit is isomorphic to the target unit.

Source: monoidal-category unit and associator identities; Stacks Project Tag 0FPT.
(blueprint: lem-sf-semigroupal-left-unit).

Proof: write a_X for the inverse tensor comparison at (1,X), followed by the
mapped left unitor. Associativity and naturality identify these isomorphisms as
an associative action of the multiplication a_1 on F(1). Tensoring on the right
by F(1) is fully faithful, because F(1) is isomorphic to the unit. Hence a_1
uniquely determines an isomorphism epsilon whose tensor with F(1) is a_1 followed
by the inverse left unitor. The action equation, associator naturality and left
unitor naturality then give a_X = epsilon tensor id followed by the left unitor,
after cancelling two isomorphisms. This includes zero and trivial categories. -/
theorem exists_leftUnit_of_associative_tensor
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D)
    (μ : MonoidalCategory.tensor C ⋙ F ≅ F.prod F ⋙ MonoidalCategory.tensor D)
    (v : F.obj (𝟙_ C) ≅ 𝟙_ D)
    (hμ : ∀ X Y Z : C,
      F.map (α_ X Y Z).hom ≫ μ.hom.app (X, Y ⊗ Z) ≫
          (F.obj X ◁ μ.hom.app (Y, Z)) =
        μ.hom.app (X ⊗ Y, Z) ≫ (μ.hom.app (X, Y) ▷ F.obj Z) ≫
          (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom) :
    ∃ ε : F.obj (𝟙_ C) ≅ 𝟙_ D, ∀ X : C,
      μ.hom.app (𝟙_ C, X) ≫ (ε.hom ▷ F.obj X) ≫ (λ_ (F.obj X)).hom =
        F.map (λ_ X).hom := by
  let a (X : C) : F.obj (𝟙_ C) ⊗ F.obj X ≅ F.obj X :=
    (μ.app (𝟙_ C, X)).symm ≪≫ F.mapIso (λ_ X)
  let t : tensorRight (F.obj (𝟙_ C)) ≅ 𝟭 D :=
    (curriedTensor D).flip.mapIso v ≪≫ rightUnitorNatIso D
  let ff := (Functor.FullyFaithful.id D).ofIso t.symm
  let ε : F.obj (𝟙_ C) ≅ 𝟙_ D :=
    ff.preimageIso (a (𝟙_ C) ≪≫ (λ_ (F.obj (𝟙_ C))).symm)
  have hε : (a (𝟙_ C)).hom = ε.hom ▷ F.obj (𝟙_ C) ≫
      (λ_ (F.obj (𝟙_ C))).hom := by
    have h := ff.map_preimage
      (a (𝟙_ C) ≪≫ (λ_ (F.obj (𝟙_ C))).symm).hom
    change ε.hom ▷ F.obj (𝟙_ C) =
      (a (𝟙_ C)).hom ≫ (λ_ (F.obj (𝟙_ C))).inv at h
    rw [h]
    simp
  have hn {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
      (F.map f ⊗ₘ F.map g) ≫ μ.inv.app (X', Y') =
        μ.inv.app (X, Y) ≫ F.map (f ⊗ₘ g) := by
    simpa only [Functor.comp_map, Functor.prod_map, tensor_map] using
      (μ.inv.naturality (X := (X, Y)) (Y := (X', Y')) (f, g))
  have hi (X Y Z : C) :
      (μ.inv.app (X, Y) ▷ F.obj Z) ≫ μ.inv.app (X ⊗ Y, Z) ≫
          F.map (α_ X Y Z).hom =
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
          (F.obj X ◁ μ.inv.app (Y, Z)) ≫ μ.inv.app (X, Y ⊗ Z) := by
    apply (cancel_epi (μ.hom.app (X ⊗ Y, Z) ≫
      (μ.hom.app (X, Y) ▷ F.obj Z))).mp
    simp only [Category.assoc, ← comp_whiskerRight_assoc, Iso.hom_inv_id_app,
      id_whiskerRight, Category.id_comp]
    rw [← reassoc_of% (hμ X Y Z)]
    simp [← whiskerLeft_comp_assoc]
  refine ⟨ε, fun X ↦ ?_⟩
  have ha : (a (𝟙_ C)).hom ▷ F.obj X ≫ (a X).hom =
      (α_ (F.obj (𝟙_ C)) (F.obj (𝟙_ C)) (F.obj X)).hom ≫
        F.obj (𝟙_ C) ◁ (a X).hom ≫ (a X).hom := by
    dsimp only [a, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom]
    rw [comp_whiskerRight]
    simp only [Category.assoc]
    have hn₁ := hn (λ_ (𝟙_ C)).hom (𝟙 X)
    simp only [F.map_id, tensorHom_id] at hn₁
    rw [reassoc_of% hn₁, ← F.map_comp]
    rw [leftUnitor_whiskerRight, Category.assoc, ← leftUnitor_naturality]
    rw [F.map_comp, F.map_comp, reassoc_of% (hi (𝟙_ C) (𝟙_ C) X)]
    have hn₂ := hn (𝟙 (𝟙_ C)) (λ_ X).hom
    simp only [F.map_id, id_tensorHom] at hn₂
    rw [← reassoc_of% hn₂]
    simp only [whiskerLeft_comp, Category.assoc]
  have h := action_unit (a (𝟙_ C)) (a X) ε hε ha
  apply (cancel_epi (μ.inv.app (𝟙_ C, X))).mp
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc, a, Iso.trans_hom,
    Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom] using h.symm

end CategoryTheory
