/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Homology.Additive

/-!
# Zero morphisms and the general-site tensor product

Source: Stacks Project, Modules on Sites, Section 03EK
(blueprint: def-pur-sheaf-tensor-product).
The existing independent-universe tensor product is retained. This module shows that tensoring
with a fixed right factor preserves zero morphisms.
-/

@[expose] public section

universe uC vC r m

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]
  {A : Sheaf J CommRingCat.{r}}

/-- Tensor with a fixed right factor preserves zero morphisms.
Source: Stacks, Section 03EK (blueprint: def-pur-sheaf-tensor-product).
Proof: sectionwise, `0 ⊗ id` vanishes on pure tensors, hence is the zero linear map.
The forgetful functor and additive module sheafification preserve zero maps as well. -/
theorem siteSheafTensorRight_preservesZeroMorphisms
    (N : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) :
    (siteSheafTensorRight N).PreservesZeroMorphisms := by
  have : (siteTensorRight N.val).PreservesZeroMorphisms := by
    refine ⟨?_⟩
    intro M M'
    ext U : 1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    change (0 : M.obj U →ₗ[A.obj.obj U] M'.obj U) x ⊗ₜ[A.obj.obj U] y = 0
    simp
  dsimp only [siteSheafTensorRight]
  infer_instance

attribute [instance] siteSheafTensorRight_preservesZeroMorphisms

end SheafOfModules

namespace SheafOfModules

section

open CategoryTheory CategoryTheory.Limits
variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]
  {A : Sheaf J CommRingCat.{r}}

set_option linter.unusedSectionVars false in
/-- The map on tensor presheaves in the second variable commutes with restrictions.
Source: Stacks, Section 03EK (blueprint: def-pur-sheaf-tensor-product).
Proof: both composites send `x ⊗ y` to the tensor of the restriction of `x` and
of the image of `y`; naturality of the second-factor morphism identifies these.
Pure tensors generate the sectionwise tensor product. -/
theorem siteTensorSecondMap_naturality
    (M : PresheafOfModules.{m} (A.obj ⋙ forget₂ CommRingCat RingCat))
    {N N' : PresheafOfModules.{m} (A.obj ⋙ forget₂ CommRingCat RingCat)} (g : N ⟶ N')
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (siteTensorPresheaf M N).map f ≫
        (ModuleCat.restrictScalars (A.obj.map f).hom).map
          (ModuleCat.ofHom (TensorProduct.map (LinearMap.id : M.obj V →ₗ[A.obj.obj V] M.obj V)
            (g.app V).hom)) =
      ModuleCat.ofHom (TensorProduct.map (LinearMap.id : M.obj U →ₗ[A.obj.obj U] M.obj U)
        (g.app U).hom) ≫ (siteTensorPresheaf M N').map f := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  exact congrArg (fun z : N'.obj V ↦ M.restrictₛₗ f x ⊗ₜ[A.obj.obj V] z)
    (PresheafOfModules.naturality_apply g f y)

/-- Tensor a presheaf morphism in the second variable, sectionwise `id ⊗ g`.
Source: Stacks, Section 03EK (blueprint: def-pur-sheaf-tensor-product). -/
noncomputable def siteTensorSecondMap
    (M : PresheafOfModules.{m} (A.obj ⋙ forget₂ CommRingCat RingCat))
    {N N' : PresheafOfModules.{m} (A.obj ⋙ forget₂ CommRingCat RingCat)} (g : N ⟶ N') :
    siteTensorPresheaf M N ⟶ siteTensorPresheaf M N' where
  app U := ModuleCat.ofHom (TensorProduct.map
    (LinearMap.id : M.obj U →ₗ[A.obj.obj U] M.obj U) (g.app U).hom)
  naturality f := siteTensorSecondMap_naturality M g f

/-- Sheafify the sectionwise map `id ⊗ g`, using the existing tensor objects.
Source: Stacks, Section 03EK (blueprint: def-pur-sheaf-tensor-product). -/
noncomputable def siteSheafTensorSecondMap
    (M : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    {N N' : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)}
    (g : N ⟶ N') : (siteSheafTensorRight N).obj M ⟶ (siteSheafTensorRight N').obj M :=
  letI := siteTensor_identity_locallyInjective
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
  letI := siteTensor_identity_locallySurjective
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
  (PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (𝟙 _)).map
      (siteTensorSecondMap M.val g.val)

/-- A local pure tensor, mapped into the sheaf tensor product by the sheafification unit.
Source: Stacks, Section 03EK (blueprint: def-pur-sheaf-tensor-product). -/
noncomputable def siteSheafTensorTmul
    (M N : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    ((siteSheafTensorRight N).obj M).val.obj U :=
  letI := siteTensor_identity_locallyInjective
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
  letI := siteTensor_identity_locallySurjective
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
  (((PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (𝟙 _)).unit.app
      (siteTensorPresheaf M.val N.val)).app U) (x ⊗ₜ[A.obj.obj U] y)

end

end SheafOfModules
