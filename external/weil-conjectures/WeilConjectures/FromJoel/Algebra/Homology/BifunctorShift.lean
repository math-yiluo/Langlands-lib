/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.BifunctorShift

/-!
# Behaviour of the action of bifunctors on cochain complexes with respect to shifts

Supplement to `Mathlib.Algebra.Homology.BifunctorShift`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

open CategoryTheory Category Limits

namespace CochainComplex

open HomologicalComplex

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

section

variable [Preadditive C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ : CochainComplex C₁ ℤ)
  {K₂ L₂ : CochainComplex C₂ ℤ} (ψ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ (X₁ : C₁), (F.obj X₁).PreservesZeroMorphisms] (x : ℤ)
  [HasMapBifunctor K₁ K₂ F] [HasMapBifunctor K₁ L₂ F]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma mapBifunctorShift₁Iso_hom_naturality₂ :
    mapBifunctorMap (𝟙 (K₁⟦x⟧)) ψ F _ ≫ (mapBifunctorShift₁Iso K₁ L₂ F x).hom =
    (mapBifunctorShift₁Iso K₁ K₂ F x).hom ≫ (mapBifunctorMap (𝟙 K₁) ψ F _)⟦x⟧' := by
  ext n p q h
  simp [mapBifunctorShift₁Iso, HomologicalComplex₂.ι_totalShift₁Iso_hom_f _ _ _ _ _ _ _ rfl _ rfl,
   HomologicalComplex₂.ι_totalShift₁Iso_hom_f_assoc _ _ _ _ _ _ _ rfl _ rfl]

end

section

variable [HasZeroMorphisms C₁] [Preadditive C₂] [Preadditive D]
  {K₁ L₁ : CochainComplex C₁ ℤ} (φ : K₁ ⟶ L₁)
  (K₂ : CochainComplex C₂ ℤ)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ (X₁ : C₁), (F.obj X₁).Additive] (y : ℤ)
  [HasMapBifunctor K₁ K₂ F] [HasMapBifunctor L₁ K₂ F]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma mapBifunctorShift₂Iso_hom_naturality₁ :
    mapBifunctorMap φ (𝟙 (K₂⟦y⟧)) F _ ≫ (mapBifunctorShift₂Iso L₁ K₂ F y).hom =
      (mapBifunctorShift₂Iso K₁ K₂ F y).hom ≫ (mapBifunctorMap φ (𝟙 (K₂)) F _)⟦y⟧' := by
  ext n p q h
  simp [mapBifunctorShift₂Iso, HomologicalComplex₂.ι_totalShift₂Iso_hom_f _ _ _ _ _ _ _ rfl _ rfl,
    HomologicalComplex₂.ι_totalShift₂Iso_hom_f_assoc _ _ _ _ _ _ _ rfl _ rfl]

end

end CochainComplex

namespace CategoryTheory.Functor

open HomologicalComplex

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]

open CochainComplex in
set_option backward.defeqAttrib.useBackward true in
/-- Shifting the first variable of the bifunctor action on cochain complexes. -/
noncomputable def map₂CochainComplexObjShiftIso (F : C₁ ⥤ C₂ ⥤ D)
    [F.Additive] [∀ (X₁ : C₁), (F.obj X₁).PreservesZeroMorphisms]
      [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ), HasMapBifunctor K₁ K₂ F]
    (K₁ : CochainComplex C₁ ℤ) (n : ℤ) :
    F.map₂CochainComplex.obj (K₁⟦n⟧) ≅ (F.map₂CochainComplex).obj K₁ ⋙ shiftFunctor _ n :=
  NatIso.ofComponents (fun K₂ ↦ mapBifunctorShift₁Iso K₁ K₂ F n)

open CochainComplex in
set_option backward.defeqAttrib.useBackward true in
/-- Shifting the second variable of the bifunctor action on cochain complexes. -/
noncomputable def map₂CochainComplexFlipObjShiftIso (F : C₁ ⥤ C₂ ⥤ D)
    [F.PreservesZeroMorphisms] [∀ (X₁ : C₁), (F.obj X₁).Additive]
      [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ), HasMapBifunctor K₁ K₂ F]
    (K₂ : CochainComplex C₂ ℤ) (n : ℤ) :
    F.map₂CochainComplex.flip.obj (K₂⟦n⟧) ≅
      F.map₂CochainComplex.flip.obj K₂ ⋙ shiftFunctor _ n :=
  NatIso.ofComponents (fun K₁ ↦ mapBifunctorShift₂Iso K₁ K₂ F n)

end CategoryTheory.Functor
