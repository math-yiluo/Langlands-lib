/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!

# Separated and proper morphisms in `Over S`

For schemes over a base scheme `S`, viewed as objects of `Over S`, we record:

* the relative diagonal `X ⟶ X ×_Y X` in `Over S` of a morphism `f : X ⟶ Y` with separated
  underlying morphism is a closed immersion
  (`AlgebraicGeometry.isClosedImmersion_pullbackDiagonal_left`);
* the product `f × f' : X ×_S X' ⟶ Y ×_S Y'` in `Over S` of morphisms with proper underlying
  morphisms is proper (`AlgebraicGeometry.isProper_prodMap_left`), being the composite of two
  base changes `f × 𝟙` and `𝟙 × f'`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.Limits.IsPullback

variable {C : Type*} [Category C]

/-- The product `𝟙 × f : X ⨯ A ⟶ X ⨯ B` is the base change of `f : A ⟶ B` along the second
projection:
```
X ⨯ A ⟶ A
  |     |
  v     v
X ⨯ B ⟶ B
```
-/
lemma of_prod_snd_with_id {A B : C} (f : A ⟶ B) (X : C) [HasBinaryProduct X A]
    [HasBinaryProduct X B] :
    IsPullback prod.snd (prod.map (𝟙 X) f) f prod.snd where
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun s ↦ by
    refine ⟨prod.lift (s.snd ≫ prod.fst) s.fst, ?_, ?_, ?_⟩
    · simp
    · apply prod.hom_ext
      · simp
      · simp [PullbackCone.condition]
    · intro m h₁ h₂
      dsimp at m h₁ h₂ ⊢
      apply prod.hom_ext
      · simp [← h₂]
      · simpa using h₁)⟩

end CategoryTheory.Limits.IsPullback

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- The relative diagonal `X ⟶ X ×_Y X` in `Over S` of a morphism `f : X ⟶ Y` whose underlying
morphism of schemes is separated is a closed immersion: the forgetful functor `Over S ⥤ Scheme`
preserves pullbacks, and identifies it with the diagonal of `f.left`. -/
instance isClosedImmersion_pullbackDiagonal_left {X Y : Over S} (f : X ⟶ Y)
    [IsSeparated f.left] : IsClosedImmersion (pullback.diagonal f).left := by
  have h := (IsPullback.of_hasPullback f f).map (Over.forget S)
  have e : (pullback.diagonal f).left = pullback.diagonal f.left ≫ h.isoPullback.inv := by
    rw [Iso.eq_comp_inv]
    apply pullback.hom_ext
    · simp [← Over.comp_left]
    · simp [← Over.comp_left]
  rw [e]
  infer_instance

/-- The product `f × f' : X ×_S X' ⟶ Y ×_S Y'` in `Over S` of morphisms with proper underlying
morphisms is proper: it is the composite of `f × 𝟙` and `𝟙 × f'`, base changes of `f` and `f'`
along the projections. -/
instance isProper_prodMap_left {X Y X' Y' : Over S} (f : X ⟶ Y) (f' : X' ⟶ Y')
    [IsProper f.left] [IsProper f'.left] : IsProper (prod.map f f').left := by
  have h₁ : IsProper (prod.map f (𝟙 X')).left :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_prod_fst_with_id f X').map (Over.forget S))
        (inferInstanceAs (IsProper f.left))
  have h₂ : IsProper (prod.map (𝟙 Y) f').left :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_prod_snd_with_id f' Y).map (Over.forget S))
        (inferInstanceAs (IsProper f'.left))
  have e : prod.map f f' = prod.map f (𝟙 X') ≫ prod.map (𝟙 Y) f' := by simp
  rw [e, Over.comp_left]
  infer_instance

end AlgebraicGeometry
