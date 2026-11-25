/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedLocalClassEdgeMap
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedSingleAdjunctionTranspose
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.CategoryTheory.RightDerivedSingleZeroUnit
import all WeilConjectures.AlgebraicGeometry.PinnedDerivedAdjunctionShifts

/-! # Invertibility in the first degree of the derived single comparison
Source: Stacks Project, derived.tex, Tag 0156; cohomology.tex, Tag 079W.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry

attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit

private theorem single_unit_iso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] (M : C) (q : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor D q).map
      (F.rightDerivedFunctorUnit.app ((HomotopyCategory.singleFunctor C q).obj M))) := by
  let H₀ := DerivedCategory.homologyFunctor D 0
  let Hq := DerivedCategory.homologyFunctor D q
  let η := F.rightDerivedFunctorUnit
  have hη : NatTrans.CommShift η ℤ := canonicalRightDerivedUnitShift F
  have hzero : IsIso (H₀.map (F.rightDerivedSingleUnit M)) := by
    have h := F.rightDerivedSingleUnit_zero M
    have : IsIso (H₀.map (F.rightDerivedSingleUnit M) ≫
        (F.homologyRightDerivedFunctorObjSingleFunctorIso M 0 ≪≫
          F.rightDerivedZeroIsoSelf.app M).hom) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (F.homologyRightDerivedFunctorObjSingleFunctorIso M 0 ≪≫
        F.rightDerivedZeroIsoSelf.app M).hom
  have hunit : IsIso (H₀.map (η.app ((HomotopyCategory.singleFunctor C 0).obj M))) := by
    have : IsIso (H₀.map (DerivedCategory.Q.map
        ((F.mapCochainComplexSingleFunctor 0).inv.app M)) ≫
      H₀.map (η.app ((HomotopyCategory.singleFunctor C 0).obj M))) := by
      simpa only [Functor.rightDerivedSingleUnit, cast_eq, Functor.map_comp,
        Functor.comp_obj, HomotopyCategory.singleFunctor, HomotopyCategory.singleFunctors,
        CochainComplex.singleFunctor, CochainComplex.singleFunctors,
        SingleFunctors.postcomp] using hzero
    exact IsIso.of_isIso_comp_left
      (H₀.map (DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app M))) _
  let K := (HomotopyCategory.singleFunctor C 0).obj M
  have hshift : IsIso (Hq.map ((η.app K)⟦-q⟧')) :=
    (NatIso.isIso_map_iff (H₀.shiftIso (-q) q 0 (by omega)) (η.app K)).2 hunit
  have hshift' : IsIso (Hq.map (η.app (K⟦-q⟧))) := by
    rw [NatTrans.app_shift η (-q) K, Functor.map_comp, Functor.map_comp]
    infer_instance
  let e : (HomotopyCategory.singleFunctor C q).obj M ≅ K⟦-q⟧ :=
    (((HomotopyCategory.singleFunctors C).shiftIso (-q) q 0 (by omega)).app M).symm
  exact (NatTrans.isIso_app_iff_of_iso (Functor.whiskerRight η Hq) e).2 hshift'

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- The single direct-image comparison is invertible on cohomology in its single degree.
Source: Stacks, Tag 0156, transported by the canonical integer shifts.
(blueprint: lem-weil-pbc-integer-single-direct-image-unit-iso).

Proof: In degree zero, the existing normalized right-derived unit is inverse to the
zeroth-derived-functor comparison for a left exact functor. The unit commutes with
integer shifts. Identify a single in degree q with the shift by -q of the degree-zero
single. Naturality of the unit and of the homology shift isomorphism transfers
invertibility to degree q. The extra source single comparison is already an isomorphism.
This argument includes negative q, zero modules, and empty schemes. -/
theorem topEdgeSingleDirectImageMap_isIso_homology {T S : Scheme.{u}} (g : T ⟶ S)
    (q : ℤ) (M : SheafOfModules.{u} (moduleRings T.toRingedSpace)) :
    IsIso ((DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q).map
        (topEdgeSingleDirectImageMap g q M)) := by
  let F := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
  have h := single_unit_iso F M q
  unfold topEdgeSingleDirectImageMap
  simp only [cast_eq]
  rw [Functor.map_comp]
  infer_instance

end AlgebraicGeometry
