/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.FromJoel.Algebra.Homology.Bifunctor
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# The monoidal category structure on homological complexes is preadditive

Supplement to `Mathlib.Algebra.Homology.Monoidal`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Category

namespace HomologicalComplex

variable {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C] [HasZeroObject C]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  {I : Type*} [AddMonoid I] {c : ComplexShape I} [c.TensorSigns]

variable (C c) [∀ (X₁ X₂ : GradedObject I C), GradedObject.HasTensor X₁ X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [DecidableEq I]

instance (K : HomologicalComplex C c) :
    ((curriedTensor (HomologicalComplex C c)).obj K).Additive :=
  inferInstanceAs
    ((Functor.map₂HomologicalComplex (curriedTensor C) c c c).obj K).Additive

instance (K : HomologicalComplex C c) :
    ((curriedTensor (HomologicalComplex C c)).flip.obj K).Additive :=
  inferInstanceAs
    ((Functor.map₂HomologicalComplex (curriedTensor C) c c c).flip.obj K).Additive

instance : MonoidalPreadditive (HomologicalComplex C c) where
  whiskerLeft_zero {_ _ _} := ((curriedTensor (HomologicalComplex C c)).obj _).map_zero _ _
  zero_whiskerRight {_ _ _} := ((curriedTensor (HomologicalComplex C c)).flip.obj _).map_zero _ _
  whiskerLeft_add _ _ :=
    ((curriedTensor (HomologicalComplex C c)).obj _).map_add
  add_whiskerRight _ _ :=
    ((curriedTensor (HomologicalComplex C c)).flip.obj _).map_add

end HomologicalComplex
