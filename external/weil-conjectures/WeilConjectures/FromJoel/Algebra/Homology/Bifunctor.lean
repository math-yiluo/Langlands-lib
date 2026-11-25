/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.TotalComplex

/-!
# Additivity of the action of bifunctors on homological complexes

Supplement to `Mathlib.Algebra.Homology.Bifunctor`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {D : Type*} [Category* D] [Preadditive D]

@[simp]
lemma mapBifunctorMap_map_add₁ {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    [Preadditive C₁] [HasZeroMorphisms C₂]
    {I₁ I₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
    {K₁ L₁ : HomologicalComplex C₁ c₁} (f g : K₁ ⟶ L₁) {K₂ L₂ : HomologicalComplex C₂ c₂}
    (h : K₂ ⟶ L₂) (F : C₁ ⥤ C₂ ⥤ D) [F.Additive]
    [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
    {J : Type*} [DecidableEq J] (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]
    [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] :
    mapBifunctorMap (f + g) h F c = mapBifunctorMap f h F c + mapBifunctorMap g h F c := by
  aesop_cat

@[simp]
lemma mapBifunctorMap_map_add₂ {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    [HasZeroMorphisms C₁] [Preadditive C₂]
    {I₁ I₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
    {K₁ L₁ : HomologicalComplex C₁ c₁} (f : K₁ ⟶ L₁) {K₂ L₂ : HomologicalComplex C₂ c₂}
    (g h : K₂ ⟶ L₂) (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X₁, (F.obj X₁).Additive]
    {J : Type*} [DecidableEq J] (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]
    [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] :
    mapBifunctorMap f (g + h) F c = mapBifunctorMap f g F c + mapBifunctorMap f h F c := by
  aesop_cat

end HomologicalComplex

namespace CategoryTheory.Functor

open HomologicalComplex

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D] [Preadditive D]

section

variable [Preadditive C₁] [HasZeroMorphisms C₂]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  {I₁ I₂ J : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c : ComplexShape J)
  [DecidableEq J] [TotalComplexShape c₁ c₂ c]
  [∀ (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂), HasMapBifunctor K₁ K₂ F c]

instance : (map₂HomologicalComplex F c₁ c₂ c).Additive where

instance (K₂ : HomologicalComplex C₂ c₂) :
    ((map₂HomologicalComplex F c₁ c₂ c).flip.obj K₂).Additive where

end

section

variable [HasZeroMorphisms C₁] [Preadditive C₂]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).Additive]
  {I₁ I₂ J : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [DecidableEq J]
  [∀ (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂), HasMapBifunctor K₁ K₂ F c]

instance : (map₂HomologicalComplex F c₁ c₂ c).flip.Additive where

instance (K₁ : HomologicalComplex C₁ c₁) :
    ((map₂HomologicalComplex F c₁ c₂ c).obj K₁).Additive where

end

end CategoryTheory.Functor
