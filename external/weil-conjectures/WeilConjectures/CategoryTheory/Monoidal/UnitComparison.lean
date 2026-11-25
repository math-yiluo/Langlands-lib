/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Comparing unit objects through a functor

For a functor `T : C ⥤ D` between monoidal categories with a tensor comparison
`T(K ⊗ M) ⟶ T K ⊗ T M` and a unit comparison `T 𝟙 ⟶ 𝟙` satisfying the left unit law, an
isomorphism `τ : T Z ≅ Z'` between "unit objects" compatible with their products corresponds to
the unit comparison
(`CategoryTheory.MonoidalCategory.map_hom_comp_eq_of_whiskerRight_comp_leftUnitor`).
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.MonoidalCategory

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]

/-- Let `T : C ⥤ D` be a functor with a tensor comparison `d : T(K ⊗ M) ⟶ T K ⊗ T M`, natural in
`K`, and a unit comparison `e : T 𝟙 ⟶ 𝟙` satisfying the left unit law. Let `Z ≅ 𝟙_ C` and
`Z' ≅ 𝟙_ D` be "unit objects" with products `Z ⊗ Z ⟶ Z` and `Z' ⊗ Z' ⟶ Z'` satisfying the left
unit law, and `τ : T Z ≅ Z'` compatible with the products. Then `τ` corresponds to `e` under the
identifications of `Z` and `Z'` with the units, i.e. the square
```
          T zC
   T Z ──────────▶ T 𝟙_C
    │                │
  τ │                │ e
    ▼                ▼
    Z' ──────────▶ 𝟙_D
           zD
```
commutes. Writing `a = T zC ≫ e` and `b = τ ≫ zD`, both
satisfy `d ≫ (a ▷ T Z) ≫ λ ≫ τ = T(Z ⊗ Z ⟶ Z) ≫ τ`, so `a ▷ T Z = b ▷ T Z`, and since `T Z` is
isomorphic to the unit, `a = b`. -/
lemma map_hom_comp_eq_of_whiskerRight_comp_leftUnitor (T : C ⥤ D)
    (d : ∀ K M : C, T.obj (K ⊗ M) ⟶ T.obj K ⊗ T.obj M)
    (hd : ∀ {K K' : C} (f : K ⟶ K') (M : C), T.map (f ▷ M) ≫ d K' M = d K M ≫ T.map f ▷ T.obj M)
    (e : T.obj (𝟙_ C) ⟶ 𝟙_ D) [IsIso e] {Z : C} {Z' : D} [Epi (d Z Z)]
    (he : d (𝟙_ C) Z ≫ e ▷ T.obj Z ≫ (λ_ (T.obj Z)).hom = T.map (λ_ Z).hom)
    (zC : Z ≅ 𝟙_ C) (zD : Z' ≅ 𝟙_ D) (addC : Z ⊗ Z ⟶ Z) (addD : Z' ⊗ Z' ⟶ Z')
    (τ : T.obj Z ≅ Z') (hC : zC.hom ▷ Z ≫ (λ_ Z).hom = addC)
    (hD : zD.hom ▷ Z' ≫ (λ_ Z').hom = addD)
    (hadd : T.map addC ≫ τ.hom = d Z Z ≫ τ.hom ▷ T.obj Z ≫ Z' ◁ τ.hom ≫ addD) :
    T.map zC.hom ≫ e = τ.hom ≫ zD.hom := by
  have h₁ : d Z Z ≫ (T.map zC.hom ≫ e) ▷ T.obj Z ≫ (λ_ _).hom = T.map addC := by
    rw [comp_whiskerRight, Category.assoc, ← hC, T.map_comp, ← he, reassoc_of% hd]
  have h₂ : d Z Z ≫ (τ.hom ≫ zD.hom) ▷ T.obj Z ≫ 𝟙_ D ◁ τ.hom ≫ (λ_ _).hom =
      T.map addC ≫ τ.hom := by
    rw [hadd, ← hD, comp_whiskerRight, Category.assoc, whisker_exchange_assoc]
  have key : (T.map zC.hom ≫ e) ▷ T.obj Z = (τ.hom ≫ zD.hom) ▷ T.obj Z := by
    rw [← cancel_epi (d Z Z), ← cancel_mono (𝟙_ D ◁ τ.hom ≫ (λ_ _).hom), Category.assoc,
      Category.assoc, h₂, leftUnitor_naturality, reassoc_of% h₁]
  have hW := congrArg (· ≫ (𝟙_ D ◁ (T.map zC.hom ≫ e))) key
  simp only [← whisker_exchange, cancel_epi] at hW
  rwa [MonoidalCategory.whiskerRight_id, MonoidalCategory.whiskerRight_id, cancel_epi,
    cancel_mono] at hW

end CategoryTheory.MonoidalCategory
