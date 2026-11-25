/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!

# Fibre products over a base

For two objects `X`, `Y` over a base `B`, this file records the structure morphism
`X ×_B Y ⟶ B` of the fibre product and the product of two morphisms over `B`.

```
  X ×_B Y --q--> Y
     |           |
     p           g
     v           v
     X ---f----> B
```

## Main definitions

- `CategoryTheory.Limits.pullback.toBase`: the structure morphism `X ×_B Y ⟶ B`.
- `CategoryTheory.Limits.pullback.mapOverBase`: the product `f₁ × f₂` of two morphisms over
  a base.
- `CategoryTheory.Limits.pullback.mapOverBaseRight`: the product `f × 𝟙` of a morphism with
  an identity over a base.
- `CategoryTheory.Limits.pullback.mapOverBaseIso`: `X₁ ×_S X₂` is the fibre product over
  `Y₁ ×_S Y₂` of the base changes of `f₁` and `f₂` to `Y₁ ×_S Y₂`.

-/

@[expose] public section

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] {S B X Y Z X₁ X₂ Y₁ Y₂ : C}

/-- The structure morphism `X ×_B Y ⟶ B` of the fibre product of `f : X ⟶ B` and
`g : Y ⟶ B`, the common composite of either projection with the corresponding leg. -/
noncomputable def pullback.toBase (f : X ⟶ B) (g : Y ⟶ B) [HasPullback f g] :
    pullback f g ⟶ B :=
  pullback.fst f g ≫ f

@[simp]
lemma pullback.fst_comp_eq_toBase (f : X ⟶ B) (g : Y ⟶ B) [HasPullback f g] :
    pullback.fst f g ≫ f = pullback.toBase f g :=
  rfl

@[simp]
lemma pullback.snd_comp_eq_toBase (f : X ⟶ B) (g : Y ⟶ B) [HasPullback f g] :
    pullback.snd f g ≫ g = pullback.toBase f g :=
  (pullback.condition).symm

/-- The product `f₁ × f₂ : X₁ ×_S X₂ ⟶ Y₁ ×_S Y₂` over a base `S` of two morphisms
`f₁ : X₁ ⟶ Y₁` and `f₂ : X₂ ⟶ Y₂`, where `X₁` and `X₂` are viewed over `S` through
`f₁ ≫ b₁` and `f₂ ≫ b₂`. -/
noncomputable def pullback.mapOverBase (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (b₁ : Y₁ ⟶ S)
    (b₂ : Y₂ ⟶ S) [HasPullback (f₁ ≫ b₁) (f₂ ≫ b₂)] [HasPullback b₁ b₂] :
    pullback (f₁ ≫ b₁) (f₂ ≫ b₂) ⟶ pullback b₁ b₂ :=
  pullback.map _ _ _ _ f₁ f₂ (𝟙 S) (by simp) (by simp)

@[reassoc (attr := simp)]
lemma pullback.mapOverBase_fst (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (b₁ : Y₁ ⟶ S) (b₂ : Y₂ ⟶ S)
    [HasPullback (f₁ ≫ b₁) (f₂ ≫ b₂)] [HasPullback b₁ b₂] :
    pullback.mapOverBase f₁ f₂ b₁ b₂ ≫ pullback.fst b₁ b₂ =
      pullback.fst (f₁ ≫ b₁) (f₂ ≫ b₂) ≫ f₁ := by
  simp [pullback.mapOverBase, pullback.map]

@[reassoc (attr := simp)]
lemma pullback.mapOverBase_snd (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (b₁ : Y₁ ⟶ S) (b₂ : Y₂ ⟶ S)
    [HasPullback (f₁ ≫ b₁) (f₂ ≫ b₂)] [HasPullback b₁ b₂] :
    pullback.mapOverBase f₁ f₂ b₁ b₂ ≫ pullback.snd b₁ b₂ =
      pullback.snd (f₁ ≫ b₁) (f₂ ≫ b₂) ≫ f₂ := by
  simp [pullback.mapOverBase, pullback.map]

/-- The product `f × 𝟙_Z : X ×_S Z ⟶ Y ×_S Z` over a base `S` of a morphism `f : X ⟶ Y`
with the identity of a further object `Z` over `S`, where `X` is viewed over `S` through
`f ≫ b`. -/
noncomputable def pullback.mapOverBaseRight (f : X ⟶ Y) (b : Y ⟶ S) (c : Z ⟶ S)
    [HasPullback (f ≫ b) c] [HasPullback b c] : pullback (f ≫ b) c ⟶ pullback b c :=
  pullback.map _ _ _ _ f (𝟙 Z) (𝟙 S) (by simp) (by simp)

@[reassoc (attr := simp)]
lemma pullback.mapOverBaseRight_fst (f : X ⟶ Y) (b : Y ⟶ S) (c : Z ⟶ S)
    [HasPullback (f ≫ b) c] [HasPullback b c] :
    pullback.mapOverBaseRight f b c ≫ pullback.fst b c =
      pullback.fst (f ≫ b) c ≫ f := by
  simp [pullback.mapOverBaseRight, pullback.map]

@[reassoc (attr := simp)]
lemma pullback.mapOverBaseRight_snd (f : X ⟶ Y) (b : Y ⟶ S) (c : Z ⟶ S)
    [HasPullback (f ≫ b) c] [HasPullback b c] :
    pullback.mapOverBaseRight f b c ≫ pullback.snd b c = pullback.snd (f ≫ b) c := by
  simp [pullback.mapOverBaseRight, pullback.map]

section MapOverBaseIso

variable [HasPullbacks C] (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (b₁ : Y₁ ⟶ S) (b₂ : Y₂ ⟶ S)

/-- The fibre product `X₁ ×_S X₂` is the fibre product over `B = Y₁ ×_S Y₂` of the base changes
`X₁ ×_{Y₁} B ⟶ B` and `X₂ ×_{Y₂} B ⟶ B` of `f₁` and `f₂`; under this identification
`f₁ × f₂` becomes the structure morphism of the fibre product over `B`
(`pullback.mapOverBaseIso_hom_toBase`). -/
noncomputable def pullback.mapOverBaseIso :
    pullback (f₁ ≫ b₁) (f₂ ≫ b₂) ≅
      pullback (pullback.snd f₁ (pullback.fst b₁ b₂)) (pullback.snd f₂ (pullback.snd b₁ b₂)) where
  hom := pullback.lift
    (pullback.lift (pullback.fst _ _) (pullback.mapOverBase f₁ f₂ b₁ b₂) (by simp))
    (pullback.lift (pullback.snd _ _) (pullback.mapOverBase f₁ f₂ b₁ b₂) (by simp))
    (by simp)
  inv := pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ pullback.fst _ _)
    (by
      simp only [Category.assoc]
      rw [pullback.condition_assoc, pullback.condition_assoc (f := f₂), pullback.condition_assoc,
        pullback.condition])
  hom_inv_id := by ext <;> simp
  inv_hom_id := by
    have h : pullback.snd (pullback.snd f₁ (pullback.fst b₁ b₂))
        (pullback.snd f₂ (pullback.snd b₁ b₂)) ≫ pullback.fst f₂ (pullback.snd b₁ b₂) ≫ f₂ =
          pullback.fst (pullback.snd f₁ (pullback.fst b₁ b₂))
            (pullback.snd f₂ (pullback.snd b₁ b₂)) ≫
            pullback.snd f₁ (pullback.fst b₁ b₂) ≫ pullback.snd b₁ b₂ := by
      rw [pullback.condition, ← pullback.condition_assoc]
    ext <;> simp [-pullback.fst_comp_eq_toBase, -pullback.snd_comp_eq_toBase,
      ← pullback.condition, h]

@[reassoc (attr := simp)]
lemma pullback.mapOverBaseIso_hom_toBase :
    (pullback.mapOverBaseIso f₁ f₂ b₁ b₂).hom ≫ pullback.toBase _ _ =
      pullback.mapOverBase f₁ f₂ b₁ b₂ := by
  simp only [pullback.mapOverBaseIso, pullback.toBase, pullback.lift_fst_assoc,
    pullback.lift_snd]

@[reassoc (attr := simp)]
lemma pullback.mapOverBaseIso_inv_fst :
    (pullback.mapOverBaseIso f₁ f₂ b₁ b₂).inv ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ := by
  simp [pullback.mapOverBaseIso]

@[reassoc (attr := simp)]
lemma pullback.mapOverBaseIso_inv_snd :
    (pullback.mapOverBaseIso f₁ f₂ b₁ b₂).inv ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.fst _ _ := by
  simp [pullback.mapOverBaseIso]

end MapOverBaseIso

end CategoryTheory.Limits
