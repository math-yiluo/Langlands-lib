/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic

/-! # The unit comparison from an ordinary image to a total derived image

## References

* Stacks, Tags 079V and 0A1G
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The single-complex direct-image comparison followed by the right-derived unit.
This is an actual morphism, without a choice of a cohomological representative. -/
def canonicalSingleDirectImageMap {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) :
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj ((pushforward f).obj M) ⟶
    (schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M) :=
  cast (by rfl) (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) (ComplexShape.up ℤ) 0).inv.app M)) ≫
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app
      ((HomotopyCategory.singleFunctor _ 0).obj M))

/-- Vanishing of positive right-derived images makes the unit comparison invertible.
No invertibility or flatness of either module is required. -/
theorem isIso_canonicalSingleDirectImageMap {X S : Scheme.{u}} (f : X ⟶ S)
    [HasInjectiveResolutions X.Modules] (M : X.Modules)
    (hq : ∀ q : ℕ, 0 < q → IsZero (((pushforward f).rightDerived q).obj M)) :
    IsIso (canonicalSingleDirectImageMap f M) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let D := SheafOfModules.{u} (moduleRings S.toRingedSpace)
  let F : C ⥤ D := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  have : PreservesFiniteLimits F := by
    change PreservesFiniteLimits (pushforward f)
    infer_instance
  let R : InjectiveResolution (C := C) M := injectiveResolution M
  let K := (CochainComplex.singleFunctor C 0).obj M
  have hM : F.rightAcyclic M := fun q ↦ hq (q + 1) (by omega)
  have hK (n : ℤ) : F.rightAcyclic (K.X n) := by
    by_cases hn : n = 0
    · subst n
      exact F.rightAcyclic.prop_of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).symm hM
    · exact F.rightAcyclic.prop_of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
  have hR (n : ℤ) : F.rightAcyclic (R.cochainComplex.X n) :=
    F.rightAcyclic_of_injective _
  have hFi := F.quasiIso_map_of_rightAcyclic R.ι' 0 hK hR
  have : R.cochainComplex.IsKInjective :=
    CochainComplex.isKInjective_of_injective R.cochainComplex 0
  let Q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  have h₁ : IsIso (DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map (Q.map R.ι'))) := by
    change IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex _).map R.ι'))
    infer_instance
  have h₂ : IsIso (F.rightDerivedFunctor.map (DerivedCategory.Qh.map (Q.map R.ι'))) := by
    have : IsIso (DerivedCategory.Qh.map (Q.map R.ι')) := by
      change IsIso (DerivedCategory.Q.map R.ι')
      infer_instance
    infer_instance
  have h₃ : IsIso (F.rightDerivedFunctorUnit.app (Q.obj R.cochainComplex)) :=
    inferInstance
  have hn := F.rightDerivedFunctorUnit.naturality (Q.map R.ι')
  dsimp only [Functor.comp_map] at hn
  have := h₁
  have := h₂
  have := h₃
  have hu : IsIso (F.rightDerivedFunctorUnit.app (Q.obj K)) := by
    have : IsIso (F.rightDerivedFunctorUnit.app (Q.obj K) ≫
        F.rightDerivedFunctor.map (DerivedCategory.Qh.map (Q.map R.ι'))) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (F.rightDerivedFunctor.map (DerivedCategory.Qh.map (Q.map R.ι')))
  have : IsIso ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app
      ((HomotopyCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M)) := by
    exact hu
  unfold canonicalSingleDirectImageMap
  simp only [cast_eq]
  infer_instance

end AlgebraicGeometry.Scheme.Modules
