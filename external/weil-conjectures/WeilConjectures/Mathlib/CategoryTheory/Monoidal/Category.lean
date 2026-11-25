/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!

# Whiskering lemmas in a monoidal category

## Main statements

- `CategoryTheory.MonoidalCategory.whiskerRight_comp_leftUnitor_hom_comp`: two morphisms into
  the unit can be applied in either order.
- `CategoryTheory.MonoidalCategory.whiskerRight_injective_of_tensorIso`: if `X ⊗ Y ≅ 𝟙_ C`,
  then `- ▷ X` is injective on morphisms.

-/

@[expose] public section

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- Two morphisms into the unit can be applied in either order: the square
```
           f ▷ B
  A ⊗ B ---------> 𝟙 ⊗ B
    |                 |
  A ◁ g          (λ_ B) ≫ g
    v                 v
  A ⊗ 𝟙 ---------->   𝟙
        (ρ_ A) ≫ f
```
commutes. -/
lemma whiskerRight_comp_leftUnitor_hom_comp {A B : C} (f : A ⟶ 𝟙_ C) (g : B ⟶ 𝟙_ C) :
    f ▷ B ≫ (λ_ B).hom ≫ g = A ◁ g ≫ (ρ_ A).hom ≫ f := by
  rw [← leftUnitor_naturality, ← whisker_exchange_assoc, ← rightUnitor_naturality,
    unitors_equal]

/-- If `e : X ⊗ Y ≅ 𝟙_ C`, then `- ▷ X` is injective on morphisms: every `k : Z ⟶ Z'` is
recovered from `k ▷ X` as the composite
```
       ρ⁻¹          Z ◁ e⁻¹                α⁻¹                (k ▷ X) ▷ Y
  Z -------> Z ⊗ 𝟙 --------> Z ⊗ (X ⊗ Y) -----> (Z ⊗ X) ⊗ Y -------------> (Z' ⊗ X) ⊗ Y

       α            Z' ◁ e               ρ
  ----> Z' ⊗ (X ⊗ Y) -------> Z' ⊗ 𝟙 -------> Z'.
```
-/
lemma whiskerRight_injective_of_tensorIso {X Y : C} (e : X ⊗ Y ≅ 𝟙_ C) {Z Z' : C}
    {f g : Z ⟶ Z'} (h : f ▷ X = g ▷ X) : f = g := by
  have key (k : Z ⟶ Z') : k = (ρ_ Z).inv ≫ Z ◁ e.inv ≫ (α_ Z X Y).inv ≫ (k ▷ X) ▷ Y ≫
      (α_ Z' X Y).hom ≫ Z' ◁ e.hom ≫ (ρ_ Z').hom := by
    rw [← whiskerRight_tensor_assoc, ← whisker_exchange_assoc, ← whiskerLeft_comp_assoc,
      e.inv_hom_id, whiskerLeft_id, Category.id_comp, rightUnitor_naturality,
      Iso.inv_hom_id_assoc]
  rw [key f, key g, h]

end CategoryTheory.MonoidalCategory
