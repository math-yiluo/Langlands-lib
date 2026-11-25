/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedScalarTensorComparison
public import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.Algebra.Homology.RingedTensorComplexConstraints

/-! # Pure sections of the scalar tensor comparison

Source: Stacks Project, section-tensor-product (03EK).
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.ConstantCompletion
open MonoidalCategory CategoryTheory.CochainPullback

namespace CategoryTheory.ConstantCompletion

variable {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}
  {R S : Sheaf T CommRingCat.{w}}

attribute [local instance] SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory
attribute [local implicit_reducible] SheafOfModules.unit SheafOfModules.restrictScalars
  CategoryTheory.sheafCompose change PresheafOfModules.restrictScalars
  PresheafOfModules.toPresheaf

/-- The constructed ordinary module comparison sends x tensor s to s tensor x.
Source: Stacks Project, section-tensor-product (03EK).
(auxiliary; not a blueprint node). -/
theorem scalarTensorModuleIso_pure (f : R ⟶ S) (M : Mod R)
    (V : Cᵒᵖ) (x : M.val.obj V) (s : S.obj.obj V) :
    (scalarTensorModuleIso f M).hom.val.app V
        (moduleTmul (R := R) M (scalarTensorModule f) V x s) =
      tensorSection f M V s x := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.monoidalCategory S
  let e := (SheafOfModules.exists_changeOfRings_tensorCancellation_sections f).choose
  have hc := (SheafOfModules.exists_changeOfRings_tensorCancellation_sections f).choose_spec.2
    (SheafOfModules.unit (siteModuleRings S)) M V (1 : S.obj.obj V) s x
  change (e (SheafOfModules.unit (siteModuleRings S)) M).hom.val.app V
      (moduleTmul (R := S) (SheafOfModules.unit (siteModuleRings S))
        ((change f).obj M) V (1 : S.obj.obj V) (tensorSection f M V s x)) =
    moduleTmul (R := R) (scalarTensorModule f) M V (s * (1 : S.obj.obj V)) x at hc
  rw [mul_one] at hc
  have hi : (e (SheafOfModules.unit (siteModuleRings S)) M).inv.val.app V
      (moduleTmul (R := R) (scalarTensorModule f) M V s x) =
    moduleTmul (R := S) (SheafOfModules.unit (siteModuleRings S))
      ((change f).obj M) V (1 : S.obj.obj V) (tensorSection f M V s x) := by
    rw [← hc]
    exact congrArg (fun k ↦ k.val.app V
      (moduleTmul (R := S) (SheafOfModules.unit (siteModuleRings S))
        ((change f).obj M) V (1 : S.obj.obj V) (tensorSection f M V s x)))
      (e (SheafOfModules.unit (siteModuleRings S)) M).hom_inv_id
  change ((res f).map (λ_ ((change f).obj M)).hom).val.app V
      ((e (SheafOfModules.unit (siteModuleRings S)) M).inv.val.app V
        ((β_ M (scalarTensorModule f)).hom.val.app V
          (moduleTmul (R := R) M (scalarTensorModule f) V x s))) = _
  rw [moduleTmul_braiding (R := R) M (scalarTensorModule f) V x s, hi]
  exact (CategoryTheory.RingedDerivedNative.pureTensor_leftUnitor.{w, w, w} T S
    ((change f).obj M) V (1 : S.obj.obj V) (tensorSection f M V s x)).trans
      (one_smul _ _)

/-- The ordinary right unitor inverse inserts the section one.
Source: Stacks Project, section-tensor-product (03EK).
(auxiliary; not a blueprint node). -/
theorem scalarTensorRightUnit_pure (M : Mod R) (V : Cᵒᵖ) (x : M.val.obj V) :
    (ρ_ M).inv.val.app V x =
      moduleTmul (R := R) M (SheafOfModules.unit (siteModuleRings R)) V x
        (1 : R.obj.obj V) := by
  have h := CategoryTheory.RingedDerivedNative.pureTensor_rightUnitor.{w, w, w} T R M V
    (1 : R.obj.obj V) x
  have hh := congrArg ((ρ_ M).inv.val.app V) h
  have hh' := (by
    simpa only [CategoryTheory.RingedDerivedNative.pureTensor,
      CategoryTheory.RingedDerivedNative.moduleMonoidal,
      SheafOfModules.cochainModulesMonoidal, one_smul,
      ← ModuleCat.comp_apply, ← PresheafOfModules.comp_app, ← SheafOfModules.comp_val,
      Iso.hom_inv_id, SheafOfModules.id_val, PresheafOfModules.id_app,
      ModuleCat.id_apply] using hh.symm : _)
  convert hh' using 1

end CategoryTheory.ConstantCompletion
