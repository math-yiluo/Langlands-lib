/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.FormalFibreCohomology
@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
set_option linter.unusedVariables false in
/-- Degree-zero stalk comparison, obtained from the augmentation of the zeroth
right-derived direct image.
Proof: Apply the degree-zero augmentation comparison and take the stalk;
this gives the displayed equivalence.
(blueprint: lem-weil-pbc-formal-functions-degree-zero-stalk-iso) -/
theorem formalFunctions_degreeZero_stalkIso {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    ∃ a : (((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))) ≃ₗ[
          Y.presheaf.stalk y]
        formalFunctionsStalk f y (SheafOfModules.unit X.ringCatSheaf) 0), True := by
  let : PreservesFiniteLimits
      (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) := by
    change PreservesFiniteLimits (Scheme.Modules.pushforward f)
    infer_instance
  have hi : IsIso ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).toRightDerivedZero.app
      (SheafOfModules.unit X.ringCatSheaf)) := by infer_instance
  let gcat := (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).map
    ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).toRightDerivedZero.app
      (SheafOfModules.unit X.ringCatSheaf))
  have hgi : IsIso gcat := by dsimp [gcat]; infer_instance
  let g : _ →ₗ[Y.presheaf.stalk y] _ := gcat.hom
  have hgb : Function.Bijective g := (ConcreteCategory.isIso_iff_bijective gcat).mp hgi
  exact ⟨LinearEquiv.ofBijective g hgb, trivial⟩
end AlgebraicGeometry
