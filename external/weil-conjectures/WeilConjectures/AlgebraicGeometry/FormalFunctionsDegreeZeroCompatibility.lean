/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.FormalFibreCohomology
import WeilConjectures.AlgebraicGeometry.FormalFunctionsDegreeZeroAugmentationCompatibility
@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
/-- There are degree-zero identifications for which every canonical theta carries
augmentation classes to pullback of sections. The stalk equivalence has precisely
the canonical degree-zero augmentation as its underlying linear map.
Source: Stacks Project, Tags 01E4 and 01FB, degree-zero augmentation constructions.
Proof: Take the stalk of the direct-image augmentation. Left exactness makes it
an isomorphism, so its underlying linear map gives a linear equivalence a.
The augmentation compatibility lemma supplies b and the germ equation for this
fixed map; the linear equivalence has that map as its underlying function.
(blueprint: lem-weil-pbc-formal-functions-degree-zero-compatibility) -/
theorem formalFunctions_degreeZero_compatibility {X Y : Scheme.{u}}
    (f : X ⟶ Y) (y : Y) :
    ∃ a : ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))) ≃ₗ[
          Y.presheaf.stalk y]
        formalFunctionsStalk f y (SheafOfModules.unit X.ringCatSheaf) 0,
      a.toLinearMap = ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).map
        ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).toRightDerivedZero.app
          (SheafOfModules.unit X.ringCatSheaf))).hom ∧
      ∃ b : formalFibreCohomologySystem f y (SheafOfModules.unit X.ringCatSheaf) 0 ≅
          formalFibreSectionsSystem f y,
        ∀ (n : ℕ)
          (θ : formalFunctionsStalk f y (SheafOfModules.unit X.ringCatSheaf) 0 →ₗ[
            Y.presheaf.stalk y]
            formalFibreCohomologyLocal f y (SheafOfModules.unit X.ringCatSheaf) 0 n),
          IsFormalFunctionsTheta f y (SheafOfModules.unit X.ringCatSheaf) 0 n θ →
          ∀ (V : Y.Opens) (hy : y ∈ V)
            (hV : (⊤ : (formalFibre f y n).Opens) ≤
              (formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)) (t : Γ(X, f ⁻¹ᵁ V)),
            (b.hom.app (op n)) (θ (a (TopCat.Presheaf.germ
              ((Scheme.Modules.pushforward f).obj
                (SheafOfModules.unit X.ringCatSheaf)).val.presheaf V y hy t))) =
              (formalFibreι f y n).appLE (f ⁻¹ᵁ V) ⊤ hV t := by
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
  obtain ⟨b, hb⟩ := formalFunctions_degreeZero_augmentation_compatibility f y
  exact ⟨LinearEquiv.ofBijective g hgb, rfl, b, hb⟩
end AlgebraicGeometry
