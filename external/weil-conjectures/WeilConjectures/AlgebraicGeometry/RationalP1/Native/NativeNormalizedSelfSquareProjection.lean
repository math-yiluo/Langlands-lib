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
import all WeilConjectures.CategoryTheory.Native.NativeForwardSelfSquareProjection
import WeilConjectures.AlgebraicGeometry.RationalP1.NormalizedProjectionAdjunctionTranspose
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Trace.TraceBaseChangeFirst

/-! # Native normalized forward projection squares

The adjunction-mate square is expressed using the same bundled tensor and exchange
maps as the rational projective-line calculation. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward false
set_option synthInstance.maxSize 4096
set_option Elab.async false
open CategoryTheory MonoidalCategory
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Functor

attribute [local irreducible] traceAbstractMate traceProjectionFromComparison

private theorem mate_formula
    {C D V : Type*} [Category C] [Category D] [Category V]
    {F : C ⥤ D} {P : D ⥤ C} {U₁ U₂ : D ⥤ V} {Q : V ⥤ D}
    (a : F ⊣ P) (b : U₂ ⊣ Q) (s : F ⋙ U₂ ≅ F ⋙ U₁) :
    (mateEquiv a b (TwoSquare.mk _ _ _ _ s.hom)) =
      traceAbstractMate a b s := by
  unfold traceAbstractMate
  rfl

private theorem substitute_forward_square
    {C D V : Type*} [Category C] [Category D] [Category V]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory V]
    (F : C ⥤ D) (P : D ⥤ C) (U₁ U₂ : D ⥤ V) (Q : V ⥤ D)
    (a : F ⊣ P) (b : U₂ ⊣ Q) (s t : F ⋙ U₂ ≅ F ⋙ U₁)
    (ex : P ⋙ F ⟶ U₁ ⋙ Q)
    (dF : ∀ A B, F.obj (A ⊗ B) ⟶ F.obj A ⊗ F.obj B)
    (d₁ : ∀ A B, U₁.obj (A ⊗ B) ⟶ U₁.obj A ⊗ U₁.obj B)
    (d₂ : ∀ A B, U₂.obj (A ⊗ B) ⟶ U₂.obj A ⊗ U₂.obj B)
    (K : C) (T : D)
    (π₀ : K ⊗ P.obj T ⟶ P.obj (F.obj K ⊗ T))
    (π₂ : F.obj K ⊗ Q.obj (U₁.obj T) ⟶ Q.obj (U₂.obj (F.obj K) ⊗ U₁.obj T))
    (hp₀ : π₀ = traceProjectionFromComparison a dF K T)
    (hp₂ : π₂ = traceProjectionFromComparison b d₂ (F.obj K) (U₁.obj T))
    (he : ex = traceAbstractMate a b t) (hs : s = t)
    (h : ForwardTensorSquare
      { monoidalC := inferInstance, monoidalD := inferInstance, monoidalV := inferInstance,
        tensorF := dF, tensorOne := d₁, tensorTwo := d₂ } P Q a b t) :
    F.map π₀ ≫ ex.app (F.obj K ⊗ T) ≫
      Q.map (d₁ (F.obj K) T ≫ tensorHom (s.inv.app K) (𝟙 (U₁.obj T))) =
      dF K (P.obj T) ≫ (F.obj K ◁ ex.app T) ≫ π₂ := by
  rw [hp₀, hp₂, he, hs]
  exact forward_tensor_component dF d₁ d₂ P Q a b t h K T

universe u u₁ u₂ u₃
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
attribute [local instance 20000]
  CondensedRing.projectionModuleAbelian CondensedRing.projectionModuleHasDerived
  CondensedRing.projectionModuleCategory CondensedRing.projectionCoefficientMonObj
  CondensedRing.projectionSheafMonoidal CondensedRing.projectionModuleMonoidal
open DiagonalCoefficients CondensedRing
attribute [local implicit_reducible] ProjectionFamily
/-- The native exchange for a chosen self-square, with module-object endpoints. -/
def nativeSelfSquareExchange
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y W : Scheme.{u}}
    (f : X ⟶ Y) (p q : W ⟶ X) (sq : ChosenCartesianSquare p q f f) :
    moduleObjectDerivedPushforward Λ f ⋙ moduleObjectDerivedPullback Λ f ⟶
      moduleObjectDerivedPullback Λ p ⋙ moduleObjectDerivedPushforward Λ q := by
  unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
  exact condensedAmbientExchange Λ sq

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory DerivedCategory.Qh Functor.leftDerivedTensorComparison
  Functor.leftDerivedFunctorCounit Mod.monoidalClosed DerivedCategory.braidedCategory'
  Sheaf.monObj_sheafCompose_obj AlgebraicGeometry.ProEtale.upperStarFromPoint
  NatTrans.vcomp CondensedRing.upperStar CondensedRing.lowerStar
attribute [local irreducible] condensedAmbientExchange nativeSelfSquareExchange
  nativeProjectionTensorIso

private theorem comparison_trace
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y W : Scheme.{u}}
    (f : X ⟶ Y) (p q : W ⟶ X) (sq : ChosenCartesianSquare p q f f) :
    ambientPullbackComparison Λ sq =
      tracePullSquare Λ f p
        q sq.w := by
  unfold ambientPullbackComparison tracePullSquare tracePullComp tracePull
    moduleObjectDerivedPullback condensedAmbientPullbackComparison
  rfl

private theorem comparison_ambient
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y W : Scheme.{u}}
    (f : X ⟶ Y) (p q : W ⟶ X) (sq : ChosenCartesianSquare p q f f) :
    ambientPullbackComparison Λ sq =
      condensedAmbientPullbackComparison Λ sq := by
  unfold ambientPullbackComparison
  rfl

private theorem exchange_ambient
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y W : Scheme.{u}}
    (f : X ⟶ Y) (p q : W ⟶ X) (sq : ChosenCartesianSquare p q f f) :
    nativeSelfSquareExchange Λ f p q sq =
      traceAbstractMate (CondensedRing.derivedUpperStarLowerStarAdjunction
        Λ f)
        (CondensedRing.derivedUpperStarLowerStarAdjunction Λ q)
        (ambientPullbackComparison Λ sq) := by
  trans traceAbstractMate (CondensedRing.derivedUpperStarLowerStarAdjunction
    Λ f)
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ q)
    (condensedAmbientPullbackComparison Λ sq)
  · unfold nativeSelfSquareExchange condensedAmbientExchange
    exact mate_formula _ _ _
  · exact congrArg
      (fun s : moduleObjectDerivedPullback Λ f ⋙
          moduleObjectDerivedPullback Λ q ≅
          moduleObjectDerivedPullback Λ f ⋙
          moduleObjectDerivedPullback Λ p ↦
        traceAbstractMate (CondensedRing.derivedUpperStarLowerStarAdjunction
          Λ f)
          (CondensedRing.derivedUpperStarLowerStarAdjunction Λ q) s)
      (comparison_ambient Λ f p q sq).symm

private theorem exchange_trace
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y W : Scheme.{u}}
    (f : X ⟶ Y) (p q : W ⟶ X) (sq : ChosenCartesianSquare p q f f) :
    nativeSelfSquareExchange Λ f p q sq =
      traceAbstractMate (traceAdjunction Λ f)
        (traceAdjunction Λ q)
        (tracePullSquare Λ f p
          q sq.w) := by
  rw [exchange_ambient, ← traceAdjunction.eq_def, ← traceAdjunction.eq_def,
    comparison_trace]
  rfl

private def bundled_data
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y W : Scheme.{u}}
    (f : X ⟶ Y) (p q : W ⟶ X) :
    ForwardTensorData (moduleObjectDerivedPullback Λ f)
      (moduleObjectDerivedPullback Λ p) (moduleObjectDerivedPullback Λ q) where
  monoidalC := internalMonoidal Λ Y
  monoidalD := internalMonoidal Λ X
  monoidalV := internalMonoidal Λ W
  tensorF K T := (nativeProjectionTensorIso Λ f K T).hom
  tensorOne K T := (nativeProjectionTensorIso Λ p K T).hom
  tensorTwo K T := (nativeProjectionTensorIso Λ q K T).hom

private theorem bundled_tensorF_heq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y W : Scheme.{u}}
    (f : X ⟶ Y) (p q : W ⟶ X) (K T : DerivedCategory (Modules Λ Y)) :
    HEq (nativeProjectionTensorIso Λ f K T).hom
      ((bundled_data Λ f p q).tensorF K T) := by
  rfl

private theorem bundled_tensorOne_heq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y W : Scheme.{u}}
    (f : X ⟶ Y) (p q : W ⟶ X) (K T : DerivedCategory (Modules Λ X)) :
    HEq (nativeProjectionTensorIso Λ p K T).hom
      ((bundled_data Λ f p q).tensorOne K T) := by
  rfl

private theorem bundled_tensorTwo_heq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y W : Scheme.{u}}
    (f : X ⟶ Y) (p q : W ⟶ X) (K T : DerivedCategory (Modules Λ X)) :
    HEq (nativeProjectionTensorIso Λ q K T).hom
      ((bundled_data Λ f p q).tensorTwo K T) := by
  rfl

private def module_data
    {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [SymmetricCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [SymmetricCategory D] [MonoidalPreadditive D] [MonoidalClosed D]
    [Abelian.HasFunctorialFlatResolution D]
    {V : Type u₃} [Category.{u + 1} V] [Abelian V] [IsGrothendieckAbelian.{u + 1} V]
    [MonoidalCategory V] [SymmetricCategory V] [MonoidalPreadditive V] [MonoidalClosed V]
    [Abelian.HasFunctorialFlatResolution V]
    (RC : C) [MonObj RC] [hRCc : IsCommMonObj RC]
    (RD : D) [MonObj RD] [hRDc : IsCommMonObj RD]
    (RV : V) [MonObj RV] [hRVc : IsCommMonObj RV]
    (F : Mod C RC ⥤ Mod D RD) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [hFflat : F.PreservesFlat] [F.IsLeftAdjoint] [hFmon : F.Monoidal]
    (U₁ U₂ : Mod D RD ⥤ Mod V RV)
    [U₁.Additive] [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
    [h1flat : U₁.PreservesFlat] [U₁.IsLeftAdjoint] [h1mon : U₁.Monoidal]
    [U₂.Additive] [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
    [h2flat : U₂.PreservesFlat] [U₂.IsLeftAdjoint] [h2mon : U₂.Monoidal]
    : TraceComparisonData F.leftDerivedFunctor U₁.leftDerivedFunctor U₂.leftDerivedFunctor :=
  moduleTraceComparisonData RC RD RV F U₁ U₂

attribute [local instance 20000]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  projectionModuleMonoidal projectionModuleAbelian projectionModuleHasDerived
  projectionDerivedMonoidal projectionCoefficientMonObj projectionSheafMonoidal
  projectionModuleCategory
  traceModuleGrothendieck traceModuleFlat
  traceTensorLeft traceTensorRight traceGradedTensor traceGradedTensorLeft
  traceGradedTensorRight traceGradedTensorFour in
private theorem native_data_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y W : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (p q : W ⟶ X) :
    traceNativeComparisonData Λ f p q = module_data
      (hRCc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ Y)
      (hRDc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ X)
      (hRVc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ W)
      (hFflat := condensedUpperStarPreservesFlat Λ f)
      (h1flat := condensedUpperStarPreservesFlat Λ p)
      (h2flat := condensedUpperStarPreservesFlat Λ q)
      (hFmon := condensedUpperStarMonoidal Λ f)
      (h1mon := condensedUpperStarMonoidal Λ p)
      (h2mon := condensedUpperStarMonoidal Λ q)
      (condensedRingObj Λ Y) (condensedRingObj Λ X) (condensedRingObj Λ W)
      (CondensedRing.upperStar Λ f) (CondensedRing.upperStar Λ p)
      (CondensedRing.upperStar Λ q) := by
  unfold traceNativeComparisonData module_data
  rfl

private theorem bundled_monoidal_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    internalMonoidal Λ X = projectionDerivedMonoidal Λ X := by
  unfold internalMonoidal internalTensorBundle nativeTensorBundle projectionDerivedMonoidal
  rfl

attribute [local instance 20000]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  projectionModuleMonoidal projectionModuleAbelian projectionModuleHasDerived
  projectionDerivedMonoidal projectionCoefficientMonObj projectionSheafMonoidal
  projectionModuleCategory
  traceModuleGrothendieck traceModuleFlat
  traceTensorLeft traceTensorRight traceGradedTensor traceGradedTensorLeft
  traceGradedTensorRight traceGradedTensorFour in
private theorem bundled_field_monoidalC
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y W : Scheme.{u}}
    (f : X ⟶ Y) (p q : W ⟶ X) :
    (forgetForwardTensorData (module_data
      (hRCc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ Y)
      (hRDc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ X)
      (hRVc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ W)
      (hFflat := condensedUpperStarPreservesFlat Λ f)
      (h1flat := condensedUpperStarPreservesFlat Λ p)
      (h2flat := condensedUpperStarPreservesFlat Λ q)
      (hFmon := condensedUpperStarMonoidal Λ f)
      (h1mon := condensedUpperStarMonoidal Λ p)
      (h2mon := condensedUpperStarMonoidal Λ q)
      (condensedRingObj Λ Y) (condensedRingObj Λ X) (condensedRingObj Λ W)
      (CondensedRing.upperStar Λ f) (CondensedRing.upperStar Λ p)
      (CondensedRing.upperStar Λ q))).monoidalC = (bundled_data Λ f p q).monoidalC := by
  dsimp only [forgetForwardTensorData, module_data, moduleTraceComparisonData,
    derivedTraceComparisonData, bundled_data]
  exact (bundled_monoidal_eq Λ Y).symm

attribute [local instance 20000]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  projectionModuleMonoidal projectionModuleAbelian projectionModuleHasDerived
  projectionDerivedMonoidal projectionCoefficientMonObj projectionSheafMonoidal
  projectionModuleCategory
  traceModuleGrothendieck traceModuleFlat
  traceTensorLeft traceTensorRight traceGradedTensor traceGradedTensorLeft
  traceGradedTensorRight traceGradedTensorFour in
private theorem bundled_field_monoidalD
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y W : Scheme.{u}}
    (f : X ⟶ Y) (p q : W ⟶ X) :
    (forgetForwardTensorData (module_data
      (hRCc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ Y)
      (hRDc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ X)
      (hRVc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ W)
      (hFflat := condensedUpperStarPreservesFlat Λ f)
      (h1flat := condensedUpperStarPreservesFlat Λ p)
      (h2flat := condensedUpperStarPreservesFlat Λ q)
      (hFmon := condensedUpperStarMonoidal Λ f)
      (h1mon := condensedUpperStarMonoidal Λ p)
      (h2mon := condensedUpperStarMonoidal Λ q)
      (condensedRingObj Λ Y) (condensedRingObj Λ X) (condensedRingObj Λ W)
      (CondensedRing.upperStar Λ f) (CondensedRing.upperStar Λ p)
      (CondensedRing.upperStar Λ q))).monoidalD = (bundled_data Λ f p q).monoidalD := by
  dsimp only [forgetForwardTensorData, module_data, moduleTraceComparisonData,
    derivedTraceComparisonData, bundled_data]
  exact (bundled_monoidal_eq Λ X).symm

attribute [local instance 20000]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  projectionModuleMonoidal projectionModuleAbelian projectionModuleHasDerived
  projectionDerivedMonoidal projectionCoefficientMonObj projectionSheafMonoidal
  projectionModuleCategory
  traceModuleGrothendieck traceModuleFlat
  traceTensorLeft traceTensorRight traceGradedTensor traceGradedTensorLeft
  traceGradedTensorRight traceGradedTensorFour in
private theorem bundled_field_monoidalV
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y W : Scheme.{u}}
    (f : X ⟶ Y) (p q : W ⟶ X) :
    (forgetForwardTensorData (module_data
      (hRCc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ Y)
      (hRDc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ X)
      (hRVc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ W)
      (hFflat := condensedUpperStarPreservesFlat Λ f)
      (h1flat := condensedUpperStarPreservesFlat Λ p)
      (h2flat := condensedUpperStarPreservesFlat Λ q)
      (hFmon := condensedUpperStarMonoidal Λ f)
      (h1mon := condensedUpperStarMonoidal Λ p)
      (h2mon := condensedUpperStarMonoidal Λ q)
      (condensedRingObj Λ Y) (condensedRingObj Λ X) (condensedRingObj Λ W)
      (CondensedRing.upperStar Λ f) (CondensedRing.upperStar Λ p)
      (CondensedRing.upperStar Λ q))).monoidalV = (bundled_data Λ f p q).monoidalV := by
  dsimp only [forgetForwardTensorData, module_data, moduleTraceComparisonData,
    derivedTraceComparisonData, bundled_data]
  exact (bundled_monoidal_eq Λ W).symm

attribute [local instance 20000]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  projectionModuleMonoidal projectionModuleAbelian projectionModuleHasDerived
  projectionDerivedMonoidal projectionCoefficientMonObj projectionSheafMonoidal
  projectionModuleCategory
  traceModuleGrothendieck traceModuleFlat
  traceTensorLeft traceTensorRight traceGradedTensor traceGradedTensorLeft
  traceGradedTensorRight traceGradedTensorFour in
private theorem bundled_field_tensorF
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y W : Scheme.{u}}
    (f : X ⟶ Y) (p q : W ⟶ X) :
    ∀ K T, HEq ((forgetForwardTensorData (module_data
      (hRCc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ Y)
      (hRDc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ X)
      (hRVc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ W)
      (hFflat := condensedUpperStarPreservesFlat Λ f)
      (h1flat := condensedUpperStarPreservesFlat Λ p)
      (h2flat := condensedUpperStarPreservesFlat Λ q)
      (hFmon := condensedUpperStarMonoidal Λ f)
      (h1mon := condensedUpperStarMonoidal Λ p)
      (h2mon := condensedUpperStarMonoidal Λ q)
      (condensedRingObj Λ Y) (condensedRingObj Λ X) (condensedRingObj Λ W)
      (CondensedRing.upperStar Λ f) (CondensedRing.upperStar Λ p)
      (CondensedRing.upperStar Λ q))).tensorF K T) ((bundled_data Λ f p q).tensorF K T) := by
  intro K T
  exact HEq.trans (module_tensorF_heq
      (hRCc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ Y)
      (hRDc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ X)
      (hRVc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ W)
      (hFflat := condensedUpperStarPreservesFlat Λ f)
      (h1flat := condensedUpperStarPreservesFlat Λ p)
      (h2flat := condensedUpperStarPreservesFlat Λ q)
      (hFmon := condensedUpperStarMonoidal Λ f)
      (h1mon := condensedUpperStarMonoidal Λ p)
      (h2mon := condensedUpperStarMonoidal Λ q)
      (condensedRingObj Λ Y) (condensedRingObj Λ X) (condensedRingObj Λ W)
      (CondensedRing.upperStar Λ f) (CondensedRing.upperStar Λ p)
      (CondensedRing.upperStar Λ q) K T)
    (HEq.trans (native_projection_tensor_hom Λ f K T)
      (bundled_tensorF_heq Λ f p q K T))

attribute [local instance 20000]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  projectionModuleMonoidal projectionModuleAbelian projectionModuleHasDerived
  projectionDerivedMonoidal projectionCoefficientMonObj projectionSheafMonoidal
  projectionModuleCategory
  traceModuleGrothendieck traceModuleFlat
  traceTensorLeft traceTensorRight traceGradedTensor traceGradedTensorLeft
  traceGradedTensorRight traceGradedTensorFour in
private theorem bundled_field_tensorOne
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y W : Scheme.{u}}
    (f : X ⟶ Y) (p q : W ⟶ X) :
    ∀ K T, HEq ((forgetForwardTensorData (module_data
      (hRCc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ Y)
      (hRDc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ X)
      (hRVc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ W)
      (hFflat := condensedUpperStarPreservesFlat Λ f)
      (h1flat := condensedUpperStarPreservesFlat Λ p)
      (h2flat := condensedUpperStarPreservesFlat Λ q)
      (hFmon := condensedUpperStarMonoidal Λ f)
      (h1mon := condensedUpperStarMonoidal Λ p)
      (h2mon := condensedUpperStarMonoidal Λ q)
      (condensedRingObj Λ Y) (condensedRingObj Λ X) (condensedRingObj Λ W)
      (CondensedRing.upperStar Λ f) (CondensedRing.upperStar Λ p)
      (CondensedRing.upperStar Λ q))).tensorOne K T) ((bundled_data Λ f p q).tensorOne K T) := by
  intro K T
  exact HEq.trans (module_tensorOne_heq
      (hRCc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ Y)
      (hRDc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ X)
      (hRVc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ W)
      (hFflat := condensedUpperStarPreservesFlat Λ f)
      (h1flat := condensedUpperStarPreservesFlat Λ p)
      (h2flat := condensedUpperStarPreservesFlat Λ q)
      (hFmon := condensedUpperStarMonoidal Λ f)
      (h1mon := condensedUpperStarMonoidal Λ p)
      (h2mon := condensedUpperStarMonoidal Λ q)
      (condensedRingObj Λ Y) (condensedRingObj Λ X) (condensedRingObj Λ W)
      (CondensedRing.upperStar Λ f) (CondensedRing.upperStar Λ p)
      (CondensedRing.upperStar Λ q) K T)
    (HEq.trans (native_projection_tensor_hom Λ p K T)
      (bundled_tensorOne_heq Λ f p q K T))

attribute [local instance 20000]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  projectionModuleMonoidal projectionModuleAbelian projectionModuleHasDerived
  projectionDerivedMonoidal projectionCoefficientMonObj projectionSheafMonoidal
  projectionModuleCategory
  traceModuleGrothendieck traceModuleFlat
  traceTensorLeft traceTensorRight traceGradedTensor traceGradedTensorLeft
  traceGradedTensorRight traceGradedTensorFour in
private theorem bundled_field_tensorTwo
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y W : Scheme.{u}}
    (f : X ⟶ Y) (p q : W ⟶ X) :
    ∀ K T, HEq ((forgetForwardTensorData (module_data
      (hRCc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ Y)
      (hRDc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ X)
      (hRVc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ W)
      (hFflat := condensedUpperStarPreservesFlat Λ f)
      (h1flat := condensedUpperStarPreservesFlat Λ p)
      (h2flat := condensedUpperStarPreservesFlat Λ q)
      (hFmon := condensedUpperStarMonoidal Λ f)
      (h1mon := condensedUpperStarMonoidal Λ p)
      (h2mon := condensedUpperStarMonoidal Λ q)
      (condensedRingObj Λ Y) (condensedRingObj Λ X) (condensedRingObj Λ W)
      (CondensedRing.upperStar Λ f) (CondensedRing.upperStar Λ p)
      (CondensedRing.upperStar Λ q))).tensorTwo K T) ((bundled_data Λ f p q).tensorTwo K T) := by
  intro K T
  exact HEq.trans (module_tensorTwo_heq
      (hRCc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ Y)
      (hRDc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ X)
      (hRVc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ W)
      (hFflat := condensedUpperStarPreservesFlat Λ f)
      (h1flat := condensedUpperStarPreservesFlat Λ p)
      (h2flat := condensedUpperStarPreservesFlat Λ q)
      (hFmon := condensedUpperStarMonoidal Λ f)
      (h1mon := condensedUpperStarMonoidal Λ p)
      (h2mon := condensedUpperStarMonoidal Λ q)
      (condensedRingObj Λ Y) (condensedRingObj Λ X) (condensedRingObj Λ W)
      (CondensedRing.upperStar Λ f) (CondensedRing.upperStar Λ p)
      (CondensedRing.upperStar Λ q) K T)
    (HEq.trans (native_projection_tensor_hom Λ q K T)
      (bundled_tensorTwo_heq Λ f p q K T))

attribute [local instance 20000]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  projectionModuleMonoidal projectionModuleAbelian projectionModuleHasDerived
  projectionDerivedMonoidal projectionCoefficientMonObj projectionSheafMonoidal
  projectionModuleCategory
  traceModuleGrothendieck traceModuleFlat
  traceTensorLeft traceTensorRight traceGradedTensor traceGradedTensorLeft
  traceGradedTensorRight traceGradedTensorFour in
private theorem bundled_data_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y W : Scheme.{u}}
    (f : X ⟶ Y) (p q : W ⟶ X) :
    forgetForwardTensorData (module_data
      (hRCc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ Y)
      (hRDc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ X)
      (hRVc := AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ W)
      (hFflat := condensedUpperStarPreservesFlat Λ f)
      (h1flat := condensedUpperStarPreservesFlat Λ p)
      (h2flat := condensedUpperStarPreservesFlat Λ q)
      (hFmon := condensedUpperStarMonoidal Λ f)
      (h1mon := condensedUpperStarMonoidal Λ p)
      (h2mon := condensedUpperStarMonoidal Λ q)
      (condensedRingObj Λ Y) (condensedRingObj Λ X) (condensedRingObj Λ W)
      (CondensedRing.upperStar Λ f) (CondensedRing.upperStar Λ p)
      (CondensedRing.upperStar Λ q)) = bundled_data Λ f p q := by
  exact forward_tensor_data_ext _ _ (bundled_field_monoidalC Λ f p q)
    (bundled_field_monoidalD Λ f p q) (bundled_field_monoidalV Λ f p q)
    (bundled_field_tensorF Λ f p q) (bundled_field_tensorOne Λ f p q)
    (bundled_field_tensorTwo Λ f p q)

-- Transport the equation while its tensor structures remain bundled.
private theorem bundled_forward_square
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y W : Scheme.{u}}
    (f : X ⟶ Y) (p q : W ⟶ X) (sq : ChosenCartesianSquare p q f f) :
    ForwardTensorSquare (bundled_data Λ f p q)
      (tracePush Λ f) (tracePush Λ q) (traceAdjunction Λ f) (traceAdjunction Λ q)
      (tracePullSquare Λ f p q sq.w) := by
  exact forward_tensor_transport (traceNativeComparisonData Λ f p q) _
    (bundled_data Λ f p q) (native_data_eq Λ f p q) (bundled_data_eq Λ f p q)
    (tracePush Λ f) (tracePush Λ q) (traceAdjunction Λ f) (traceAdjunction Λ q)
    (tracePullSquare Λ f p q sq.w)
    (native_forward_self_square_projection Λ f p q sq.w)

attribute [local instance 30000] internalMonoidal in
-- Fix the bundled tensor interface before exposing the normalized projection.
private theorem bundled_projection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (a : ProjectionFamily Λ) (ha : ProjectionNormalized Λ a)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Modules Λ Y)) (T : DerivedCategory (Modules Λ X)) :
    a f K T = traceProjectionFromComparison (traceAdjunction Λ f)
      (fun A B ↦ (nativeProjectionTensorIso Λ f A B).hom) K T := by
  exact eq_of_heq (normalized_projection_transpose Λ a ha f K T)

attribute [local irreducible] CondensedRing.leftDerivedUpperStarTensor
attribute [local irreducible] ForwardTensorSquare
end AlgebraicGeometry.ProEtale.RationalP1
