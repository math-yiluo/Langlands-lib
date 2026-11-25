/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # Left-unit coherence for composite tensor comparisons -/
@[expose] public section
set_option autoImplicit false
open CategoryTheory MonoidalCategory
namespace CategoryTheory

/-- Left-unit coherence pastes under composition of tensor functors.
Source: Stacks 07A4 (blueprint: lem-pur-composite-left-unit-coherence).
Proof: expand the composite unit. Naturality of the second tensor comparison
moves the image of the first unit to the left of that comparison. Apply the
second left-unit law and functoriality, then apply the first left-unit law. -/
theorem composite_left_unit
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (F : C ⥤ D) (G : D ⥤ E)
    (dF : ∀ X Y : C, F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y)
    (dG : ∀ X Y : D, G.obj (X ⊗ Y) ≅ G.obj X ⊗ G.obj Y)
    (hdG : ∀ {X Y : D} (f : X ⟶ Y) (Z : D),
      G.map (f ▷ Z) ≫ (dG Y Z).hom =
        (dG X Z).hom ≫ (G.map f ▷ G.obj Z))
    (eF : F.obj (𝟙_ C) ≅ 𝟙_ D) (eG : G.obj (𝟙_ D) ≅ 𝟙_ E)
    (hF : ∀ X, (dF (𝟙_ C) X).hom ≫ eF.hom ▷ F.obj X ≫
      (λ_ (F.obj X)).hom = F.map (λ_ X).hom)
    (hG : ∀ X, (dG (𝟙_ D) X).hom ≫ eG.hom ▷ G.obj X ≫
      (λ_ (G.obj X)).hom = G.map (λ_ X).hom)
    (X : C) :
    G.map ((dF (𝟙_ C) X).hom) ≫ (dG (F.obj (𝟙_ C)) (F.obj X)).hom ≫
        (G.map eF.hom ≫ eG.hom) ▷ G.obj (F.obj X) ≫
        (λ_ (G.obj (F.obj X))).hom = G.map (F.map (λ_ X).hom) := by
  have hn := hdG eF.hom (F.obj X)
  simp only [comp_whiskerRight, Category.assoc]
  rw [← reassoc_of% hn, hG, ← G.map_comp, ← G.map_comp, hF]

end CategoryTheory
