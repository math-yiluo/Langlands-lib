/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import all Mathlib.Algebra.Homology.Localization

/-! # AffineSinglePushforwardUnitIso

Source: Stacks Project, finite duality and affine cohomology
(blueprint: lem-sc-affine-single-pushforward-unit-iso). -/

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The canonical right-derived unit computes affine pushforward of a quasi-coherent
module in degree zero, not merely some unspecified derived isomorphism.

Source: Stacks Project, Cohomology of Schemes, Tag 01XC; Derived Categories of
Schemes, Tags 08I8 and 0AVW
(blueprint: lem-sc-affine-single-pushforward-unit-iso).

Proof:
1. Affine higher-direct-image vanishing makes M acyclic for module direct image F.
   The other terms of M[0] are zero, hence F-acyclic. Direct image is left exact
   because it is right adjoint to module pullback.
2. Choose a bounded-below injective resolution i : M[0] -> I. Its terms are
   F-acyclic and I is K-injective. The theorem `quasiIso_map_of_rightAcyclic`
   makes F(i) a quasi-isomorphism, so Q(F(i)) is an isomorphism.
3. Naturality of F's right-derived unit along i says Q(F(i)) followed by the
   unit at I equals the unit at M[0] followed by RF(Q(i)). The unit at I is
   invertible since I is K-injective; RF(Q(i)) is invertible since i is a
   quasi-isomorphism. Therefore the unit at M[0] is invertible as well.
4. The single-complex comparison is already an isomorphism. Composing its
   inverse, mapped by Q, with the unit gives exactly the displayed morphism.
   Rank zero, empty schemes, and the zero module require no cancellation. -/
theorem affine_singlePushforward_unit_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (M : X.Modules) (hM : M.IsQuasicoherent) :
    IsIso (DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) (ComplexShape.up ℤ) 0).inv.app M) ≫
      (cast (by rfl) ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M))) :
        _ ⟶ (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M))) := by
  classical
  let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let : M.IsQuasicoherent := hM
  have : PreservesFiniteLimits F := by
    change PreservesFiniteLimits (Scheme.Modules.pushforward f)
    have := (Scheme.Modules.pullbackPushforwardAdjunction f).rightAdjoint_preservesLimits
    infer_instance
  have := Scheme.Modules.isGrothendieckAbelian X
  have hA : F.rightAcyclic M := by
    intro n
    exact Scheme.Modules.isZero_higherDirectImage_of_isAffineHom f M (Nat.succ_pos n)
  let K := (CochainComplex.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M
  have hK : ∀ n, F.rightAcyclic (K.X n) := by
    intro n
    by_cases hn : n = 0
    · subst n
      exact F.rightAcyclic.prop_of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).symm hA
    · exact F.rightAcyclic.prop_of_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M n hn)
  let K' : CochainComplex.Plus
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := ⟨K, 0, inferInstance⟩
  obtain ⟨I, _, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective K' 0
  let I' := (InjectiveObject.ι _).mapCochainComplexPlus.obj I
  have : QuasiIso i.hom := hi
  have : ∀ n, Injective (I'.obj.X n) := fun n ↦
    inferInstanceAs (Injective ((InjectiveObject.ι _).obj (I.obj.X n)))
  have : I'.obj.IsStrictlyGE 0 :=
    (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ _ _).2 ‹_›
  have : I'.obj.IsKInjective := CochainComplex.isKInjective_of_injective I'.obj 0
  have : QuasiIso ((F.mapHomologicalComplex _).map i.hom) :=
    F.quasiIso_map_of_rightAcyclic i.hom 0 hK (fun n ↦ Functor.rightAcyclic_of_injective _)
  let iq := (HomotopyCategory.quotient _ _).map i.hom
  have h₁ : IsIso (DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map iq)) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 ‹QuasiIso
        ((F.mapHomologicalComplex _).map i.hom)›)
  have h₂ : IsIso (F.rightDerivedFunctor.map (DerivedCategory.Qh.map iq)) := by
    have : IsIso (DerivedCategory.Qh.map iq) :=
      Localization.inverts DerivedCategory.Qh
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) _
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hi)
    infer_instance
  have h₃ : IsIso (F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj I'.obj)) := inferInstance
  have hnat := F.rightDerivedFunctorUnit.naturality iq
  dsimp only [Functor.comp_map] at hnat
  have : IsIso (F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj K'.obj) ≫
      F.rightDerivedFunctor.map (DerivedCategory.Qh.map iq)) := by
    rw [← hnat]
    infer_instance
  have : IsIso (F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj K'.obj)) :=
    IsIso.of_isIso_comp_right _ (F.rightDerivedFunctor.map (DerivedCategory.Qh.map iq))
  simp only [cast_eq]
  infer_instance

end AlgebraicGeometry
