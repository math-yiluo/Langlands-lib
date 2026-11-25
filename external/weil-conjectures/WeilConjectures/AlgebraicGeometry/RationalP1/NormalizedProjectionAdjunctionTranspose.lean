/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPretraceData
public import WeilConjectures.AlgebraicGeometry.RationalP1.Native.NativeProjectionTensorInterface
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Trace.TraceBaseChangeFirst
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.LeftCoefficientProjectionAction
/-! # The adjunction transpose of the normalized projection

This isolates the native braiding normalization from the exchange calculation. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option backward.defeqAttrib.useBackward false
set_option synthInstance.maxSize 4096
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Functor
universe u u₁ u₂

private theorem derived_left_projection
    {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [SymmetricCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] [HasColimitsOfSize.{0, 0} C]
    {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [SymmetricCategory D] [MonoidalPreadditive D] [MonoidalClosed D]
    [Abelian.HasFunctorialFlatResolution D] [HasColimitsOfSize.{0, 0} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [hFlat : F.PreservesFlat] [F.IsLeftAdjoint] [hMonoidal : F.Monoidal]
    (hF : ∀ K M : C, Functor.LaxMonoidal.μ F K M ≫ F.map (β_ K M).hom =
      (β_ (F.obj K) (F.obj M)).hom ≫ Functor.LaxMonoidal.μ F M K)
    (P : DerivedCategory D ⥤ DerivedCategory C) (a : F.leftDerivedFunctor ⊣ P)
    (K : DerivedCategory C) (N : DerivedCategory D) :
    (traceDerivedBraiding K (P.obj N)).hom ≫
      ((a.rightAdjointProjectionMap F.leftDerivedTensorComparison).app N).app K ≫
      P.map (traceDerivedBraiding N (F.leftDerivedFunctor.obj K)).hom =
    traceProjectionFromComparison a
      (fun K M ↦ (F.leftDerivedTensorComparison.app K).app M) K N := by
  let : BraidedCategory (DerivedCategory C) := DerivedCategory.braidedCategory' C
  let : SymmetricCategory (DerivedCategory C) := DerivedCategory.symmetricCategory C
  let : BraidedCategory (DerivedCategory D) := DerivedCategory.braidedCategory' D
  let : SymmetricCategory (DerivedCategory D) := DerivedCategory.symmetricCategory D
  let : F.LaxBraided := { braided := hF }
  let : F.Braided := {}
  let := F.residueDerivedMonoidal
  let : F.leftDerivedFunctor.Braided := by
    refine { braided := ?_ }
    intro A B
    apply CategoryTheory.Functor.generic_derived_braid_lax
    intro A B
    simp only [Functor.map_braiding, Category.assoc, Functor.Monoidal.μ_δ,
      Category.comp_id]
  change a.leftCoefficientProjectionMap K N = _
  exact (fixed_projection_eq a K N).symm

private theorem module_left_projection
    {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [SymmetricCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] [HasColimitsOfSize.{0, 0} C]
    {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [SymmetricCategory D] [MonoidalPreadditive D] [MonoidalClosed D]
    [Abelian.HasFunctorialFlatResolution D] [HasColimitsOfSize.{0, 0} D]
    (RC : C) [MonObj RC] [hRCc : IsCommMonObj RC]
    (RD : D) [MonObj RD] [hRDc : IsCommMonObj RD]
    (F : Mod C RC ⥤ Mod D RD) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [hFlat : F.PreservesFlat] [F.IsLeftAdjoint] [hMonoidal : F.Monoidal]
    (hF : ∀ K M : Mod C RC, Functor.LaxMonoidal.μ F K M ≫ F.map (β_ K M).hom =
      (β_ (F.obj K) (F.obj M)).hom ≫ Functor.LaxMonoidal.μ F M K)
    (P : DerivedCategory (Mod D RD) ⥤ DerivedCategory (Mod C RC)) (a : F.leftDerivedFunctor ⊣ P)
    (K : DerivedCategory (Mod C RC)) (N : DerivedCategory (Mod D RD)) :
    (traceDerivedBraiding K (P.obj N)).hom ≫
      ((a.rightAdjointProjectionMap F.leftDerivedTensorComparison).app N).app K ≫
      P.map (traceDerivedBraiding N (F.leftDerivedFunctor.obj K)).hom =
    traceProjectionFromComparison a
      (fun K M ↦ (F.leftDerivedTensorComparison.app K).app M) K N := by
  exact derived_left_projection F hF P a K N

attribute [local instance 20000]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  projectionModuleMonoidal projectionModuleAbelian projectionModuleHasDerived
  projectionDerivedMonoidal projectionCoefficientMonObj projectionSheafMonoidal
  projectionModuleCategory
  traceModuleGrothendieck traceModuleFlat
  traceTensorLeft traceTensorRight traceGradedTensor traceGradedTensorLeft
  traceGradedTensorRight traceGradedTensorFour

namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing
attribute [local implicit_reducible] ProjectionFamily
attribute [local irreducible] coefficient line twist projectionMap tensorShiftIso
attribute [local irreducible] traceDerivedBraiding DerivedCategory.braidedCategory'
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward

attribute [local irreducible] DerivedCategory.Qh
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.leftDerivedTensorComparison CategoryTheory.Functor.leftDerivedFunctorCounit
  CategoryTheory.Mod.monoidalClosed CategoryTheory.Sheaf.monObj_sheafCompose_obj
  AlgebraicGeometry.ProEtale.upperStarFromPoint NatTrans.vcomp
  CondensedRing.upperStar CondensedRing.lowerStar CategoryTheory.Functor.rightDerivedFunctor

attribute [local instance 30000] internalMonoidal in
/-- Every normalized projection family is the adjunction transpose of tensor comparison. -/
theorem normalized_projection_transpose
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (a : ProjectionFamily Λ) (ha : ProjectionNormalized Λ a) :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Modules Λ Y)) (N : DerivedCategory (Modules Λ X)),
    HEq (a f K N)
      (traceProjectionFromComparison (traceAdjunction Λ f)
        (fun A B ↦ (nativeProjectionTensorIso Λ f A B).hom) K N) := by
  unfold nativeProjectionTensorIso ProjectionFamily ProjectionNormalized internalMonoidal
    internalTensorBundle
    nativeTensorBundle at *
  intro X Y f K N
  apply HEq.trans (ha f K N)
  apply heq_of_eq
  unfold traceProjection traceBraiding tracePush tracePull
    moduleObjectDerivedPullback moduleObjectDerivedPushforward moduleObjectProjectionMate
    traceTensorComparison moduleObjectDerivedTensorComparison traceAdjunction
  dsimp only [Iso.app, asIso, id]
  rw [leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison]
  exact module_left_projection
    (hFlat := condensedUpperStarPreservesFlat Λ f)
    (hMonoidal := condensedUpperStarMonoidal Λ f)
    (hRCc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ Y)
    (hRDc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ X)
    (condensedRingObj Λ Y) (condensedRingObj Λ X)
    (CondensedRing.upperStar Λ f) (ordinary_upperStar_braiding Λ f)
    (CondensedRing.lowerStar Λ f).rightDerivedFunctor
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f) K N
end AlgebraicGeometry.ProEtale.RationalP1
