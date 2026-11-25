/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.GuitartExact.Basic

/-!
# Guitart exact squares: products

Supplement to `Mathlib.CategoryTheory.GuitartExact.Basic`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe v₁ v₂ v₃ v₄ v₁' v₂' v₃' v₄' u₁ u₂ u₃ u₄ u₁' u₂' u₃' u₄'

namespace CategoryTheory

open Limits

namespace IsConnected

variable {C D : Type*} [Category* C] [Category* D]

instance [IsConnected C] [IsConnected D] : IsConnected (C × D) := by
  apply zigzag_isConnected
  intro ⟨X₁, Y₁⟩ ⟨X₂, Y₂⟩
  exact (zigzag_obj_of_zigzag (Functor.prod' (𝟭 C) ((Functor.const C).obj Y₁))
      (isPreconnected_zigzag X₁ X₂)).trans
    (zigzag_obj_of_zigzag (Functor.prod' ((Functor.const D).obj X₂) (𝟭 D))
      (isPreconnected_zigzag Y₁ Y₂))

end IsConnected

open Category

namespace TwoSquare

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
  (w : TwoSquare T L R B)

/- The instance `[L.IsEquivalence] [R.IsEquivalence] [IsIso w.natTrans] : GuitartExact w`
from the original branch is already available in mathlib as
`TwoSquare.guitartExact_of_isEquivalence_of_isIso`. -/

section prod

variable {C₁' : Type u₁'} {C₂' : Type u₂'} {C₃' : Type u₃'} {C₄' : Type u₄'}
  [Category.{v₁'} C₁'] [Category.{v₂'} C₂'] [Category.{v₃'} C₃'] [Category.{v₄'} C₄']
  {T' : C₁' ⥤ C₂'} {L' : C₁' ⥤ C₃'} {R' : C₂' ⥤ C₄'} {B' : C₃' ⥤ C₄'}
  (w' : TwoSquare T' L' R' B')

-- `TwoSquare.prod` is provided by Mathlib (CategoryTheory.Functor.TwoSquare) since v4.35.0.

section

variable {Y₂ : C₂ × C₂'} {Y₃ : C₃ × C₃'} (g : (R.prod R').obj Y₂ ⟶ (B.prod B').obj Y₃)

namespace JRightwardsProdEquivalence

@[simp]
def functorObj (X : StructuredArrowRightwards (w.prod w') g) :
    (StructuredArrowRightwards w g.1) × (StructuredArrowRightwards w' g.2) :=
  ⟨StructuredArrowRightwards.mk w g.1 _ X.hom.left.1 X.right.hom.1 (by
      simpa only [Category.comp_id] using! dsimp% congr($(X.hom.w).fst)),
    StructuredArrowRightwards.mk w' g.2 _ X.hom.left.2 X.right.hom.2 (by
      simpa only [Category.comp_id] using! dsimp% congr($(X.hom.w).snd))⟩

@[simps]
def functor : StructuredArrowRightwards (w.prod w') g ⥤
    (StructuredArrowRightwards w g.1) × (StructuredArrowRightwards w' g.2) where
  obj X := functorObj w w' g X
  map {X Y} f :=
    ⟨StructuredArrow.homMk (CostructuredArrow.homMk f.right.left.1) (by
        have := (StructuredArrow.w f).symm
        cat_disch),
      StructuredArrow.homMk (CostructuredArrow.homMk f.right.left.2) (by
        have := (StructuredArrow.w f).symm
        cat_disch)⟩

@[simp]
def inverseObj (X : (StructuredArrowRightwards w g.1) × (StructuredArrowRightwards w' g.2)) :
  StructuredArrowRightwards (w.prod w') g :=
  StructuredArrowRightwards.mk _ _ ⟨X.1.right.left, X.2.right.left⟩
    ⟨X.1.hom.left, X.2.hom.left⟩ ⟨X.1.right.hom, X.2.right.hom⟩ (by
      dsimp
      ext
      · simpa only [Category.comp_id] using! dsimp% X.1.hom.w
      · simpa only [Category.comp_id] using! dsimp% X.2.hom.w)

@[simps]
def inverse : (StructuredArrowRightwards w g.1) × (StructuredArrowRightwards w' g.2) ⥤
    StructuredArrowRightwards (w.prod w') g where
  obj X := inverseObj w w' g X
  map {X Y} f := StructuredArrow.homMk
    (CostructuredArrow.homMk ⟨f.1.right.left, f.2.right.left⟩) (by
      have := StructuredArrow.w f.1
      have := StructuredArrow.w f.2
      cat_disch)

end JRightwardsProdEquivalence

set_option backward.isDefEq.respectTransparency false in
@[simps]
def StructuredArrowRightwardsProdEquivalence :
    StructuredArrowRightwards (w.prod w') g ≌
      (StructuredArrowRightwards w g.1) × (StructuredArrowRightwards w' g.2) where
  functor := JRightwardsProdEquivalence.functor w w' g
  inverse := JRightwardsProdEquivalence.inverse w w' g
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end

instance GuitartExact.prod [w.GuitartExact] [w'.GuitartExact] :
    (w.prod w').GuitartExact := by
  rw [guitartExact_iff_isConnected_rightwards]
  rintro Y₂ Y₃ g
  exact isConnected_of_equivalent (StructuredArrowRightwardsProdEquivalence w w' g).symm

end prod

end TwoSquare

end CategoryTheory
