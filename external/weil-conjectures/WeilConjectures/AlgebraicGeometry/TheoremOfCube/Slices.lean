/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.AlgebraicGeometry.Over

/-!
# Slices of products over a base

For schemes `A`, `B` over `S` and a section `a` of `A`, the slice `B ⟶ A ×_S B`,
`b ↦ (a, b)`, is the base change of `a` along the first projection. Consequently its ideal sheaf
is the pullback of the ideal sheaf of `a`.

Products are taken in the cartesian monoidal category `Over S`.

## Main statements

- `AlgebraicGeometry.isPullback_lift_toUnit_comp_left`: the slice is a base change of the point.
- `AlgebraicGeometry.ker_lift_toUnit_comp_left`: its ideal sheaf.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- **The slice `b ↦ (a, b)` is a base change of `a`.** For objects `A`, `B` of `Over S` and a
section `a : 𝟙 ⟶ A`, the square formed by the slice `B ⟶ A ⊗ B`, the projection
`A ⊗ B ⟶ A`, the structure map of `B` and `a` is a pullback square of schemes. -/
lemma isPullback_lift_toUnit_comp_left (A B : Over S) (a : 𝟙_ (Over S) ⟶ A) :
    IsPullback (lift (toUnit B ≫ a) (𝟙 B)).left B.hom (fst A B).left a.left := by
  have t : IsPullback (snd A B).left (fst A B).left B.hom A.hom :=
    (IsPullback.of_hasPullback A.hom B.hom).flip
  refine IsPullback.of_right (h₁₂ := (snd A B).left) (h₂₂ := A.hom) ?_ ?_ t
  · have h1 : (lift (toUnit B ≫ a) (𝟙 B)).left ≫ (snd A B).left = 𝟙 B.left := by
      rw [← Over.comp_left, lift_snd, Over.id_left]
    have h2 : a.left ≫ A.hom = 𝟙 S := Over.w a
    rw [h1, h2]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  · rw [← Over.comp_left, lift_fst, Over.comp_left]
    rfl

/-- The ideal sheaf of a base change of a closed immersion is the pullback of its ideal
sheaf. -/
lemma _root_.CategoryTheory.IsPullback.ker_fst_eq_comap {P A B C : Scheme.{u}} {fst : P ⟶ A}
    {snd : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C} (h : IsPullback fst snd f g) [IsClosedImmersion g] :
    fst.ker = g.ker.comap f := by
  rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

/-- The ideal sheaf of the slice `b ↦ (a, b)` is the pullback of the ideal sheaf of `a`. -/
lemma ker_lift_toUnit_comp_left (A B : Over S) (a : 𝟙_ (Over S) ⟶ A)
    [IsClosedImmersion a.left] :
    (lift (toUnit B ≫ a) (𝟙 B)).left.ker = a.left.ker.comap (fst A B).left := by
  exact (isPullback_lift_toUnit_comp_left A B a).ker_fst_eq_comap

variable (X Y Z : Over S)

/-- The slice `{x} × Y × Z` of `X × Y × Z` is a base change of the point `x`. -/
lemma isPullback_slice_left (x : 𝟙_ (Over S) ⟶ X) :
    IsPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)).left (Y ⊗ Z).hom
      (fst (X ⊗ Y) Z ≫ fst X Y).left x.left := by
  refine (isPullback_lift_toUnit_comp_left X (Y ⊗ Z) x).of_iso (Iso.refl _)
    ((Over.forget S).mapIso (α_ X Y Z).symm) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp, Functor.mapIso_hom, Over.forget_map,
      Iso.symm_hom, ← Over.comp_left]
    congr 1
    ext <;> simp
  · simp
  · simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom, Over.forget_map,
      Iso.symm_hom, ← Over.comp_left]
    congr 1
    simp
  · simp

/-- The slice `X × {y} × Z` of `X × Y × Z` is a base change of the point `y`. -/
lemma isPullback_slice_right (y : 𝟙_ (Over S) ⟶ Y) :
    IsPullback (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)).left (X ⊗ Z).hom
      (fst (X ⊗ Y) Z ≫ snd X Y).left y.left := by
  refine (isPullback_lift_toUnit_comp_left Y (X ⊗ Z) y).of_iso (Iso.refl _)
    ((Over.forget S).mapIso ((α_ Y X Z).symm ≪≫ whiskerRightIso (β_ Y X) Z)) (Iso.refl _)
    (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp, Functor.mapIso_hom, Over.forget_map,
      ← Over.comp_left]
    congr 1
    ext <;> simp
  · simp
  · simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom, Over.forget_map,
      ← Over.comp_left]
    congr 1
    simp
  · simp

end AlgebraicGeometry
