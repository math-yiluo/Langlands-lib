/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange

import all Mathlib.CategoryTheory.Equivalence
import all Mathlib.CategoryTheory.Iso
import all Mathlib.CategoryTheory.Shift.InducedShiftSequence

/-! # Naturality of degree-one evaluation

Source: Stacks Tag 05TD, naturality and compatibility with shifts of derived transformations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v' w' d e
open CategoryTheory

namespace CategoryTheory

attribute [local implicit_reducible] Functor.shift Functor.ShiftSequence.induced
  DerivedCategory.Plus.homologyFunctor

/-- Evaluation of a degree-one morphism commutes with a transformation of shifted functors.
The hypothesis on degree zero is the augmentation square, and the second hypothesis is
only the square of degree-one morphisms before applying either derived functor.
Source: Stacks Tag 05TD.
Proof: naturality of the transformation moves it across the degree-one morphism.
Its shift compatibility then moves it past the shift comparison. Naturality of the
homology shift identifies the resulting degree-one map. Apply the prescribed
coefficient square and the augmentation equation.
(blueprint: aux-lem-pur-coordinate-degree-one-naturality). -/
theorem degree_one_evaluation_naturality
    {T : Type u} [Category.{v} T] [HasShift T ℤ]
    {T' : Type u'} [Category.{v'} T'] [HasShift T' ℤ]
    {D : Type w} [Category.{w'} D] [Abelian D] [HasDerivedCategory.{d} D]
    (L : T ⥤ T') [L.CommShift ℤ]
    (R : T ⥤ DerivedCategory.Plus D) [R.CommShift ℤ]
    (R' : T' ⥤ DerivedCategory.Plus D) [R'.CommShift ℤ]
    (η : R ⟶ L ⋙ R') [NatTrans.CommShift η ℤ]
    {A B : T} {A' B' : T'} (a : L.obj A ⟶ A') (b : L.obj B ⟶ B')
    (x : A ⟶ B⟦(1 : ℤ)⟧) (y : A' ⟶ B'⟦(1 : ℤ)⟧)
    (square : L.map x ≫ (L.commShiftIso (1 : ℤ)).hom.app B ≫ b⟦(1 : ℤ)⟧' = a ≫ y)
    {M : D} (u : M ⟶ (DerivedCategory.Plus.homologyFunctor D 0).obj (R.obj A))
    (u' : M ⟶ (DerivedCategory.Plus.homologyFunctor D 0).obj (R'.obj A'))
    (unit : u ≫ (DerivedCategory.Plus.homologyFunctor D 0).map
      (η.app A ≫ R'.map a) = u') :
    u ≫ (DerivedCategory.Plus.homologyFunctor D 0).map
        (R.map x ≫ (R.commShiftIso (1 : ℤ)).hom.app B) ≫
      ((DerivedCategory.Plus.homologyFunctor D 0).shiftIso (1 : ℤ) 0 1
        (add_zero 1)).hom.app (R.obj B) ≫
      (DerivedCategory.Plus.homologyFunctor D 1).map (η.app B ≫ R'.map b) =
    u' ≫ (DerivedCategory.Plus.homologyFunctor D 0).map
        (R'.map y ≫ (R'.commShiftIso (1 : ℤ)).hom.app B') ≫
      ((DerivedCategory.Plus.homologyFunctor D 0).shiftIso (1 : ℤ) 0 1
        (add_zero 1)).hom.app (R'.obj B') := by
  let H := DerivedCategory.Plus.homologyFunctor D 0
  have hn := η.naturality x
  have hs := NatTrans.shift_app_comm η (1 : ℤ) B
  have hb := (R'.commShiftIso (1 : ℤ)).hom.naturality b
  simp only [Functor.comp_map] at hn hb
  simp only [Functor.commShiftIso_comp_hom_app] at hs
  have h : R.map x ≫ (R.commShiftIso (1 : ℤ)).hom.app B ≫
      (η.app B ≫ R'.map b)⟦(1 : ℤ)⟧' =
    (η.app A ≫ R'.map a) ≫ R'.map y ≫ (R'.commShiftIso (1 : ℤ)).hom.app B' := by
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    erw [reassoc_of% hs, reassoc_of% hn]
    erw [← hb, ← R'.map_comp_assoc, ← R'.map_comp_assoc, Category.assoc, square,
      R'.map_comp]
    simp only [Category.assoc]
  have hh := H.shiftIso_hom_naturality (1 : ℤ) 0 1 (add_zero 1)
    (η.app B ≫ R'.map b)
  erw [← hh, ← H.map_comp_assoc, Category.assoc, h, H.map_comp_assoc,
    ← Category.assoc u, unit]

end CategoryTheory
