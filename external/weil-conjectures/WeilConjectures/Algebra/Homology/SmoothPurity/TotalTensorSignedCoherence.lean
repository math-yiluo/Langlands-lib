/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Tactic.Ring

/-! # Signed coherence of total cochain tensors

Source: Stacks Project, Tag 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe c v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory WeilConjectures
namespace CategoryTheory.RingedDerivedNative

section Formulas

universe uA vA
variable {A : Type uA} [Category.{vA} A] [Preadditive A] [HasZeroObject A]
  [MonoidalCategory A] [MonoidalPreadditive A] [BraidedCategory A]
  [∀ (X Y : GradedObject ℤ A), X.HasTensor Y]
  [∀ X : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X)]
  [∀ X : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X)]
  [∀ (W X Y Z : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X Y Z]

end Formulas

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})

end CategoryTheory.RingedDerivedNative
