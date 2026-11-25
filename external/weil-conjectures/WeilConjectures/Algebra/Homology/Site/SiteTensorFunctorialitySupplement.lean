/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality

/-!
# Functoriality and local pure tensors for the general-site tensor product

Source: Stacks Project, Modules on Sites, Section 03EK
(blueprint: def-pur-sheaf-tensor-product).
The existing independent-universe tensor product is retained. This module exposes its
zero preservation, its action in the second variable and its sheafification-unit pure tensors.
-/

@[expose] public section

universe uC vC r m

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]
  {A : Sheaf J CommRingCat.{r}}

attribute [instance] siteSheafTensorRight_preservesZeroMorphisms

-- Keep the existing sheafification parameters in this theorem's public signature.
set_option linter.unusedSectionVars false in
/-- The map in the second variable is natural in the first variable.
Source: Stacks, Section 03EK (blueprint: def-pur-sheaf-tensor-product).
Proof: before sheafification both composites send `x ⊗ y` to `f(x) ⊗ g(y)`.
Tensor induction gives equality, and sheafification preserves that equality. -/
theorem siteSheafTensorSecondMap_naturality
    {M M' N N' : SheafOfModules.{m}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)} (f : M ⟶ M') (g : N ⟶ N') :
    (siteSheafTensorRight N).map f ≫ siteSheafTensorSecondMap M' g =
      siteSheafTensorSecondMap M g ≫ (siteSheafTensorRight N').map f := by
  let S := PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (𝟙 _)
  change S.map (siteTensorHom f.val N.val) ≫ S.map (siteTensorSecondMap M'.val g.val) =
    S.map (siteTensorSecondMap M.val g.val) ≫ S.map (siteTensorHom f.val N'.val)
  rw [← S.map_comp, ← S.map_comp]
  apply congrArg S.map
  ext U : 1
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  rfl

/-- The canonical natural transformation `- ⊗ N → - ⊗ N'` induced by `g`.
Source: Stacks, Section 03EK (blueprint: def-pur-sheaf-tensor-product). -/
noncomputable def siteSheafTensorRightMap
    {N N' : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)}
    (g : N ⟶ N') : siteSheafTensorRight N ⟶ siteSheafTensorRight N' where
  app M := siteSheafTensorSecondMap M g
  naturality _ _ f := siteSheafTensorSecondMap_naturality f g

end SheafOfModules
