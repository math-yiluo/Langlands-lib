/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Linear
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy

/-!
# Linearity of the bifunctor induced on complexes and on homotopy categories

Let `F : C₁ ⥤ C₂ ⥤ D` be a bifunctor to an `R`-linear category. If `F` is `R`-linear in its
second variable, so is the induced bifunctor `F.map₂HomologicalComplex c₁ c₂ c` on homological
complexes, and so is the bifunctor `F.bifunctorMapHomotopyCategory c₁ c₂ c` it induces on
homotopy categories; similarly in the first variable. This is the `R`-linear analogue of the
additivity instances of `WeilConjectures.FromJoel.Algebra.Homology.Bifunctor`.

## Main results

- `HomologicalComplex.mapBifunctorMap_smul₁`, `HomologicalComplex.mapBifunctorMap_smul₂`:
  `mapBifunctorMap` commutes with the scalar action in each variable.
- The instances `((F.map₂HomologicalComplex c₁ c₂ c).obj K₁).Linear R`,
  `((F.map₂HomologicalComplex c₁ c₂ c).flip.obj K₂).Linear R` and their counterparts for
  `F.bifunctorMapHomotopyCategory c₁ c₂ c`.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {D : Type*} [Category* D] [Preadditive D] (R : Type*) [Ring R] [Linear R D]

@[simp]
lemma mapBifunctorMap_smul₁ {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    [Preadditive C₁] [Linear R C₁] [HasZeroMorphisms C₂]
    {I₁ I₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
    {K₁ L₁ : HomologicalComplex C₁ c₁} (r : R) (f : K₁ ⟶ L₁) {K₂ L₂ : HomologicalComplex C₂ c₂}
    (g : K₂ ⟶ L₂) (F : C₁ ⥤ C₂ ⥤ D) [F.Additive]
    [∀ X₁, (F.obj X₁).PreservesZeroMorphisms] [∀ X₂, (F.flip.obj X₂).Linear R]
    {J : Type*} [DecidableEq J] (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]
    [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] :
    mapBifunctorMap (r • f) g F c = r • mapBifunctorMap f g F c := by
  have hF (X₂ : C₂) {Y₁ Z₁ : C₁} (φ : Y₁ ⟶ Z₁) :
      (F.map (r • φ)).app X₂ = r • (F.map φ).app X₂ :=
    (F.flip.obj X₂).map_smul r φ
  ext j i₁ i₂ h
  simp [hF]

@[simp]
lemma mapBifunctorMap_smul₂ {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    [HasZeroMorphisms C₁] [Preadditive C₂] [Linear R C₂]
    {I₁ I₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
    {K₁ L₁ : HomologicalComplex C₁ c₁} (f : K₁ ⟶ L₁) {K₂ L₂ : HomologicalComplex C₂ c₂}
    (r : R) (g : K₂ ⟶ L₂) (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X₁, (F.obj X₁).Additive] [∀ X₁, (F.obj X₁).Linear R]
    {J : Type*} [DecidableEq J] (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]
    [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] :
    mapBifunctorMap f (r • g) F c = r • mapBifunctorMap f g F c := by
  ext j i₁ i₂ h
  simp [Functor.map_smul]

end HomologicalComplex

namespace CategoryTheory.Functor

open HomologicalComplex

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D] [Preadditive D]
  (R : Type*) [Ring R] [CategoryTheory.Linear R D]

section

variable [Preadditive C₁] [CategoryTheory.Linear R C₁] [HasZeroMorphisms C₂]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  [∀ X₂, (F.flip.obj X₂).Linear R]
  {I₁ I₂ J : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [DecidableEq J]
  [∀ (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂), HasMapBifunctor K₁ K₂ F c]

instance (K₂ : HomologicalComplex C₂ c₂) :
    ((map₂HomologicalComplex F c₁ c₂ c).flip.obj K₂).Linear R where
  map_smul _ _ := mapBifunctorMap_smul₁ _ _ _ _ _ _

end

section

variable [HasZeroMorphisms C₁] [Preadditive C₂] [CategoryTheory.Linear R C₂]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).Additive]
  [∀ X₁, (F.obj X₁).Linear R]
  {I₁ I₂ J : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [DecidableEq J]
  [∀ (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂), HasMapBifunctor K₁ K₂ F c]

instance (K₁ : HomologicalComplex C₁ c₁) :
    ((map₂HomologicalComplex F c₁ c₂ c).obj K₁).Linear R where
  map_smul _ _ := mapBifunctorMap_smul₂ _ _ _ _ _ _

end

section

variable [Preadditive C₁] [CategoryTheory.Linear R C₁] [Preadditive C₂]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).Additive]
  [∀ X₂, (F.flip.obj X₂).Linear R]
  {I₁ I₂ J : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [DecidableEq J]
  [∀ (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂), HasMapBifunctor K₁ K₂ F c]

instance (K₂ : HomotopyCategory C₂ c₂) :
    ((F.bifunctorMapHomotopyCategory c₁ c₂ c).flip.obj K₂).Linear R where
  map_smul {X Y} f r := by
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C₁ c₁).map_surjective f
    rw [← Functor.map_smul]
    change (HomotopyCategory.quotient D c).map
      (((map₂HomologicalComplex F c₁ c₂ c).flip.obj K₂.as).map (r • f)) =
        r • (HomotopyCategory.quotient D c).map
          (((map₂HomologicalComplex F c₁ c₂ c).flip.obj K₂.as).map f)
    rw [Functor.map_smul, Functor.map_smul]

end

section

variable [Preadditive C₁] [Preadditive C₂] [CategoryTheory.Linear R C₂]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).Additive]
  [∀ X₁, (F.obj X₁).Linear R]
  {I₁ I₂ J : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [DecidableEq J]
  [∀ (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂), HasMapBifunctor K₁ K₂ F c]

instance (K₁ : HomotopyCategory C₁ c₁) :
    ((F.bifunctorMapHomotopyCategory c₁ c₂ c).obj K₁).Linear R where
  map_smul {X Y} f r := by
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C₂ c₂).map_surjective f
    rw [← Functor.map_smul]
    change (HomotopyCategory.quotient D c).map
      (((map₂HomologicalComplex F c₁ c₂ c).obj K₁.as).map (r • f)) =
        r • (HomotopyCategory.quotient D c).map
          (((map₂HomologicalComplex F c₁ c₂ c).obj K₁.as).map f)
    rw [Functor.map_smul, Functor.map_smul]

end

end CategoryTheory.Functor
