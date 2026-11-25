/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import all WeilConjectures.Algebra.Homology.RingedTensorComplexConstraints
import WeilConjectures.CategoryTheory.TwistedActionTensorRestriction

/-! # The normalized ordinary scalar tensor comparison

Source: Stacks Project, Modules on Sites, Tag 03EK and Tag 099M.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace CategoryTheory.ConstantCompletion.ScalarTensorComparison
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

/-- The scalar target ring, viewed as an R-module.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
abbrev scalarUnit {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) :=
  (res φ).obj (SheafOfModules.unit (siteModuleRings S))

/-- The existing normalized scalar tensor isomorphism. Its pure-tensor equation
uniquely determines its hom, so this choice introduces no unspecified data.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
@[irreducible] def scalarTensorIso {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S)
    (M : Mod R) : scalarUnit J φ ⊗ M ≅ (res φ).obj ((change φ).obj M) :=
  (SheafOfModules.exists_extensionTensorComparison φ M).choose

/-- The scalar comparison sends the pure tensor to its scalar-extension section.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
theorem scalarTensorIso_pure {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S)
    (M : Mod R) (V : Cᵒᵖ) (s : S.obj.obj V) (m : M.val.obj V) :
    (scalarTensorIso J φ M).hom.val.app V
        (SheafOfModules.RingedTensor.pure R (scalarUnit J φ) M V s m) =
      tensorSection φ M V s m :=
  by
    unfold scalarTensorIso
    exact (SheafOfModules.exists_extensionTensorComparison φ M).choose_spec V s m

/-- Reduction of the coefficient unit is the restricted target ring.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
@[irreducible] def scalarUnitIso {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) :
    scalarUnit J φ ≅ (res φ).obj ((change φ).obj (𝟙_ (Mod R))) :=
  (ρ_ (scalarUnit J φ)).symm ≪≫ scalarTensorIso J φ (𝟙_ (Mod R))

/-- The right unitor multiplies the two pure-tensor factors.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
theorem rightUnitor_pure (R : Sheaf J CommRingCat.{u})
    (M : Mod R) (V : Cᵒᵖ) (m : M.val.obj V) (x : R.obj.obj V) :
    (ρ_ M).hom.val.app V
        (SheafOfModules.RingedTensor.pure R M (𝟙_ (Mod R)) V m x) = x • m := by
  exact RingedDerivedNative.pureTensor_rightUnitor.{u, u, u} J R M V x m

/-- The inverse right unitor adjoins the coefficient section one.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
theorem rightUnitor_inv_pure (R : Sheaf J CommRingCat.{u})
    (M : Mod R) (V : Cᵒᵖ) (m : M.val.obj V) :
    (ρ_ M).inv.val.app V m =
      SheafOfModules.RingedTensor.pure R M (𝟙_ (Mod R)) V m (1 : R.obj.obj V) := by
  have h := rightUnitor_pure J R M V m 1
  have h' := congrArg ((ρ_ M).inv.val.app V) h
  have hi := congrArg (fun f ↦ f.val.app V
    (SheafOfModules.RingedTensor.pure R M (𝟙_ (Mod R)) V m
      (1 : R.obj.obj V))) (ρ_ M).hom_inv_id
  simp only [one_smul] at h'
  exact h'.symm.trans hi

/-- The coefficient-unit comparison sends s to s tensor one.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
theorem scalarUnitIso_pure {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S)
    (V : Cᵒᵖ) (s : S.obj.obj V) :
    (scalarUnitIso J φ).hom.val.app V s =
      tensorSection φ (𝟙_ (Mod R)) V s (1 : R.obj.obj V) := by
  unfold scalarUnitIso
  change (scalarTensorIso J φ (𝟙_ (Mod R))).hom.val.app V
    ((ρ_ (scalarUnit J φ)).inv.val.app V s) = _
  rw [rightUnitor_inv_pure, scalarTensorIso_pure]

/-- Tensor with the reduced coefficient unit is restricted scalar extension.
Construct it from the normalized unit comparison, tensor symmetry, and the
existing extension-tensor comparison; no quotient or derived limit is involved.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
@[irreducible] def reductionTensorIso {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S)
    (M : Mod R) :
    M ⊗ (res φ).obj ((change φ).obj (𝟙_ (Mod R))) ≅
      (res φ).obj ((change φ).obj M) :=
  (tensorLeft M).mapIso (scalarUnitIso J φ).symm ≪≫
    β_ M (scalarUnit J φ) ≪≫ scalarTensorIso J φ M

/-- The reduction comparison sends m tensor (s tensor one) to s tensor m.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
theorem reductionTensorIso_pure {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S)
    (M : Mod R) (V : Cᵒᵖ) (s : S.obj.obj V) (m : M.val.obj V) :
    (reductionTensorIso J φ M).hom.val.app V
        (SheafOfModules.RingedTensor.pure R M
          ((res φ).obj ((change φ).obj (𝟙_ (Mod R)))) V m
          (tensorSection φ (𝟙_ (Mod R)) V s (1 : R.obj.obj V))) = tensorSection φ M V s m := by
  have hi : (scalarUnitIso J φ).inv.val.app V
      (tensorSection φ (𝟙_ (Mod R)) V s (1 : R.obj.obj V)) = s := by
    rw [← scalarUnitIso_pure J φ]
    exact congrArg (fun f ↦ f.val.app V s) (scalarUnitIso J φ).hom_inv_id
  unfold reductionTensorIso
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  change (scalarTensorIso J φ M).hom.val.app V
    ((β_ M (scalarUnit J φ)).hom.val.app V
      ((M ◁ (scalarUnitIso J φ).inv).val.app V _)) = _
  rw [← id_tensorHom, SheafOfModules.RingedTensor.pure_map]
  simp only [SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply, hi]
  erw [TwistedActionRingedSite.TensorRestriction.pure_braiding]
  exact scalarTensorIso_pure J φ M V s m

/-- Pure tensors with scalar sections detect maps out of the reduction tensor.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
theorem reductionTensor_hom_ext {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S)
    (M H : Mod R)
    {f g : M ⊗ (res φ).obj ((change φ).obj (𝟙_ (Mod R))) ⟶ H}
    (h : ∀ V s m, f.val.app V
        (SheafOfModules.RingedTensor.pure R M
          ((res φ).obj ((change φ).obj (𝟙_ (Mod R)))) V m
          (tensorSection φ (𝟙_ (Mod R)) V s (1 : R.obj.obj V))) =
      g.val.app V
        (SheafOfModules.RingedTensor.pure R M
          ((res φ).obj ((change φ).obj (𝟙_ (Mod R)))) V m
          (tensorSection φ (𝟙_ (Mod R)) V s (1 : R.obj.obj V)))) : f = g := by
  apply (cancel_epi (M ◁ (scalarUnitIso J φ).hom)).1
  apply SheafOfModules.RingedTensor.pure_hom_ext R M (scalarUnit J φ)
  intro V m s
  change f.val.app V ((M ◁ (scalarUnitIso J φ).hom).val.app V _) =
    g.val.app V ((M ◁ (scalarUnitIso J φ).hom).val.app V _)
  rw [← id_tensorHom, SheafOfModules.RingedTensor.pure_map]
  simpa only [SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply,
    scalarUnitIso_pure] using h V s m

/-- The reduction tensor comparison is natural in the module.
Both composites send m tensor (s tensor one) to s tensor f(m).
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
theorem reductionTensorIso_naturality {R S : Sheaf J CommRingCat.{u}}
    (φ : R ⟶ S) {M N : Mod R} (f : M ⟶ N) :
    f ▷ (res φ).obj ((change φ).obj (𝟙_ (Mod R))) ≫
        (reductionTensorIso J φ N).hom =
      (reductionTensorIso J φ M).hom ≫ (res φ).map ((change φ).map f) := by
  apply reductionTensor_hom_ext J φ M
  intro V s m
  change (reductionTensorIso J φ N).hom.val.app V
      ((f ▷ _).val.app V _) =
    ((change φ).map f).val.app V ((reductionTensorIso J φ M).hom.val.app V _)
  rw [← tensorHom_id, SheafOfModules.RingedTensor.pure_map]
  simp only [SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply]
  rw [reductionTensorIso_pure, reductionTensorIso_pure, tensorSection_map]

end CategoryTheory.ConstantCompletion.ScalarTensorComparison
