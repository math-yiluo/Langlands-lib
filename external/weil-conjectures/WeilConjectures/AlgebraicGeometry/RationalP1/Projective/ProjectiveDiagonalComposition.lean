/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ProEtaleProjectionExchangeMaps
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientCategory

import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Finite
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Ring.ULift

/-! # Canonical direct-image section and supported-unit comparisons
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

-- Keep fixed site and derived comparisons folded during elaboration.
/-- The canonical conjugate section comparison. -/
def pushSectionIso (Y : Scheme.{u}) :
    𝟭 (DerivedCategory (Modules Λ (ProjectiveLine Y))) ≅
      CondensedRing.moduleObjectDerivedPushforward Λ (diagonalImmersion Y) ⋙
        CondensedRing.moduleObjectDerivedPushforward Λ (secondProjection Y) :=
  conjugateIsoEquiv Adjunction.id
    ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ (secondProjection Y)).comp
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (diagonalImmersion Y)))
    (pullSectionIso Λ Y (secondProjection Y) (pullback.diagonal_snd _))

set_option linter.unusedSectionVars false in
-- Keep fixed site and derived comparisons folded during elaboration.
/-- Closed direct image on internal modules is exact. -/
theorem diagonalPush_preservesFiniteColimits (Y : Scheme.{u}) :
    PreservesFiniteColimits (CondensedRing.lowerStar Λ (diagonalImmersion Y)) := by
  have := SmoothOfRelativeDimension.smooth 1 (ProjectiveLine Y ↘ Y)
  have : LocallyOfFinitePresentation (ProjectiveLine Y ↘ Y) := inferInstance
  have : LocallyOfFinitePresentation (diagonalImmersion Y) := by
    change LocallyOfFinitePresentation (pullback.diagonal (ProjectiveLine Y ↘ Y))
    infer_instance
  let E : Ab.{u + 1} ⥤ ModuleCat.{u + 1} (ULift.{u + 1} ℤ) :=
    ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (ULift.ringEquiv (R := ℤ)).symm).trans
        (forget₂ (ModuleCat.{u + 1} ℤ) Ab.{u + 1}).asEquivalence).inverse
  have he (X : Scheme.{u}) : (sheafCompose (Scheme.ProEt.topology X) E).IsEquivalence := by
    let e := E.asEquivalence
    have : (sheafCompose (Scheme.ProEt.topology X) E).EssSurj := ⟨fun P ↦
      ⟨(sheafCompose (Scheme.ProEt.topology X) e.inverse).obj P,
        ⟨ObjectProperty.isoMk _ (Functor.isoWhiskerLeft P.obj e.counitIso)⟩⟩⟩
    exact {}
  let _ := he (ProjectiveLine Y)
  let _ := he (diagonalSurface Y)
  have := ProEtale.preservesFiniteColimits_lowerStar_of_isFinite
    (ULift.{u + 1} ℤ) (diagonalImmersion Y)
  have : PreservesFiniteColimits
      (ProEtale.lowerStar Ab.{u + 1} (diagonalImmersion Y) ⋙
        sheafCompose (Scheme.ProEt.topology (diagonalSurface Y)) E) :=
    inferInstanceAs (PreservesFiniteColimits
      (sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y)) E ⋙
        ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) (diagonalImmersion Y)))
  let _ : ReflectsFiniteColimits
      (sheafCompose (Scheme.ProEt.topology (diagonalSurface Y)) E) :=
    ReflectsColimitsOfSize.reflectsFiniteColimits.{0, 0} _
  have : PreservesFiniteColimits (ProEtale.lowerStar Ab.{u + 1} (diagonalImmersion Y)) :=
    preservesFiniteColimits_of_reflects_of_preserves _
      (sheafCompose (Scheme.ProEt.topology (diagonalSurface Y)) E)
  unfold CondensedRing.lowerStar
  exact comp_preservesFiniteColimits _ _

attribute [instance] diagonalPush_preservesFiniteColimits

-- Keep fixed site and derived comparisons folded during elaboration.
/-- The actual single-degree comparison for the supported coefficient unit. -/
def supportedUnitIso (Y : Scheme.{u}) :
    (CondensedRing.moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).obj
      (unit Λ (ProjectiveLine Y)) ≅
        (DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj (source Λ Y) :=
  (CondensedRing.lowerStar Λ (diagonalImmersion Y)).singleFunctorCompRightDerivedFunctorIso.app
    (Mod.regular (condensedRingObj Λ (ProjectiveLine Y)))

/-- The literal family of left-factor projection arrows in the shared tensor interface. -/
def ProjectionFamily := ∀ {X S : Scheme.{u}} (f : X ⟶ S)
  (K : DerivedCategory (Modules Λ S)) (N : DerivedCategory (Modules Λ X)),
  K ⊗ (CondensedRing.moduleObjectDerivedPushforward Λ f).obj N ⟶
    (CondensedRing.moduleObjectDerivedPushforward Λ f).obj
      ((CondensedRing.moduleObjectDerivedPullback Λ f).obj K ⊗ N)

/-- Fix every arrow to the canonical projection, including its Koszul symmetries. -/
def ProjectionNormalized (a : ProjectionFamily Λ) : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (K : DerivedCategory (Modules Λ S))
    (N : DerivedCategory (Modules Λ X)), HEq (a f K N) (CondensedRing.traceProjection Λ f K N)

/-- The projection has a unique realization in the fixed shared tensor interface. -/
theorem projection_existsUnique : ∃! a : ProjectionFamily Λ, ProjectionNormalized Λ a := by
  unfold ProjectionFamily ProjectionNormalized internalMonoidal internalTensorBundle
    nativeTensorBundle
  refine ⟨fun f K N ↦ CondensedRing.traceProjection Λ f K N, ?_, ?_⟩
  · intro X S f K N
    rfl
  · intro a ha
    funext X S f K N
    exact eq_of_heq (ha f K N)

/-- The same canonical left projection, through its uniquely fixed interface. -/
def projectionMap : ProjectionFamily Λ := (projection_existsUnique Λ).exists.choose

end AlgebraicGeometry.ProEtale.RationalP1
