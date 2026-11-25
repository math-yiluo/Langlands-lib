/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.CategoryTheory.Native.NativeForwardSelfSquareProjection
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ProEtaleProjectionExchangeMaps
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Trace.TraceBaseChangeFirst
/-! # The native pullback tensor interface

The bundled tensorator and the canonical module derived comparison have the same map. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing
/-- The canonical pullback tensor isomorphism in the internal module tensor structure. -/
def nativeProjectionTensorIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K V : DerivedCategory (Modules Λ Y)) :
    (moduleObjectDerivedPullback Λ f).obj (K ⊗ V) ≅
      (moduleObjectDerivedPullback Λ f).obj K ⊗
        (moduleObjectDerivedPullback Λ f).obj V := by
  unfold internalMonoidal internalTensorBundle nativeTensorBundle
  exact ((traceTensorComparison Λ f).app K).app V

attribute [local irreducible] nativeProjectionTensorIso
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  DerivedCategory.Qh Functor.leftDerivedTensorComparison Functor.leftDerivedFunctorCounit
  Mod.monoidalClosed DerivedCategory.braidedCategory' Sheaf.monObj_sheafCompose_obj
  AlgebraicGeometry.ProEtale.upperStarFromPoint NatTrans.vcomp
  CondensedRing.upperStar CondensedRing.lowerStar

private theorem pull_tensor_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K V : DerivedCategory (Modules Λ Y)) :
    HEq (nativeProjectionTensorIso Λ f K V).hom
      (((moduleObjectDerivedTensorComparison Λ f).app K).app V) := by
  unfold nativeProjectionTensorIso traceTensorComparison internalMonoidal internalTensorBundle
    nativeTensorBundle
  dsimp only [Iso.app, asIso]
  rfl

attribute [local instance 20000]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  projectionModuleMonoidal projectionModuleAbelian projectionModuleHasDerived
  projectionDerivedMonoidal projectionCoefficientMonObj projectionSheafMonoidal
  projectionModuleCategory
  traceModuleGrothendieck traceModuleFlat
  traceTensorLeft traceTensorRight traceGradedTensor traceGradedTensorLeft
  traceGradedTensorRight traceGradedTensorFour in
/-- The bundled tensorator is the canonical derived comparison on internal modules. -/
theorem native_projection_tensor_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K T : DerivedCategory (Modules Λ Y)) :
    HEq (CategoryTheory.moduleDerivedTensorComparisonHom
      (hRCc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ Y)
      (hRDc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ X)
      (hFflat := condensedUpperStarPreservesFlat Λ f)
      (hFmon := condensedUpperStarMonoidal Λ f)
      (condensedRingObj Λ Y) (condensedRingObj Λ X) (CondensedRing.upperStar Λ f) K T)
      (nativeProjectionTensorIso Λ f K T).hom := by
  unfold CategoryTheory.moduleDerivedTensorComparisonHom
  rw [condensedUpperStarMonoidal_eq]
  have ht := pull_tensor_hom Λ f K T
  dsimp only [moduleObjectDerivedTensorComparison] at ht
  rw [leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison Λ f] at ht
  exact ht.symm

end AlgebraicGeometry.ProEtale.RationalP1
