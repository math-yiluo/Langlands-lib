/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.RingedDerivedTensorNative
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators

set_option linter.privateModule false

/-! # Pure-section formulas for the tensor constraints of module-sheaf complexes

Source: Stacks Project, Tag 0FPQ, and the sign rules of More on Algebra.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory WeilConjectures
open Functor.LaxMonoidal Functor.OplaxMonoidal
namespace CategoryTheory.RingedDerivedNative

section Generic
variable {A : Type*} [Category* A] [Preadditive A] [HasZeroObject A]
  [MonoidalCategory A] [MonoidalPreadditive A]
  [∀ (X Y : GradedObject ℤ A), X.HasTensor Y]
  [∀ (W X Y Z : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
  [∀ X : A, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : A, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

end Generic

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})

section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private abbrev ring :=
  (sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R

private abbrev forgetModules :=
  SheafOfModules.forget (ring.{c, v, u} J R) ⋙
    PresheafOfModules.restrictScalars (𝟙 (ring.{c, v, u} J R).obj)

private abbrev tensorAdj :=
  PresheafOfModules.sheafificationAdjunction.{max c v u} (𝟙 (ring.{c, v, u} J R).obj)

@[reducible] private noncomputable def forgetLax : (forgetModules.{c, v, u} J R).LaxMonoidal :=
  (tensorAdj.{c, v, u} J R).rightAdjointLaxMonoidal

attribute [local instance] forgetLax

private theorem forget_ε : ε (forgetModules.{c, v, u} J R) = 𝟙 _ := by
  let adj := tensorAdj.{c, v, u} J R
  have h : η (PresheafOfModules.sheafification.{max c v u}
      (𝟙 (ring.{c, v, u} J R).obj)) =
      adj.counit.app (𝟙_ (Modules.{c, v, u} J R)) := rfl
  change adj.homEquiv _ _ (η _) = _
  rw [h, Adjunction.homEquiv_unit]
  exact adj.right_triangle_components (𝟙_ (Modules.{c, v, u} J R))

private abbrev pureTensor (M N : Modules.{c, v, u} J R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :=
  CochainPullback.moduleTmul (R := R) M N U x y

private theorem pureTensor_mu (M N : Modules.{c, v, u} J R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    pureTensor.{c, v, u} J R M N U x y =
      (μ (forgetModules.{c, v, u} J R) M N).app U (x ⊗ₜ[R.obj.obj U] y) := by rfl

private theorem pureTensor_leftUnitor (M : Modules.{c, v, u} J R) (U : Cᵒᵖ)
    (a : R.obj.obj U) (x : M.val.obj U) :
    (λ_ M).hom.val.app U (pureTensor.{c, v, u} J R (𝟙_ _) M U a x) = a • x := by
  rw [pureTensor_mu]
  have h := Functor.LaxMonoidal.left_unitality (forgetModules.{c, v, u} J R) M
  rw [forget_ε, id_whiskerRight, Category.id_comp] at h
  exact congrArg (fun k ↦ k.app U (a ⊗ₜ[R.obj.obj U] x)) h.symm

private theorem pureTensor_rightUnitor (M : Modules.{c, v, u} J R) (U : Cᵒᵖ)
    (a : R.obj.obj U) (x : M.val.obj U) :
    (ρ_ M).hom.val.app U (pureTensor.{c, v, u} J R M (𝟙_ _) U x a) = a • x := by
  rw [pureTensor_mu]
  have h := Functor.LaxMonoidal.right_unitality (forgetModules.{c, v, u} J R) M
  rw [forget_ε, MonoidalCategory.whiskerLeft_id, Category.id_comp] at h
  exact congrArg (fun k ↦ k.app U (x ⊗ₜ[R.obj.obj U] a)) h.symm

end

section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

end

end CategoryTheory.RingedDerivedNative
