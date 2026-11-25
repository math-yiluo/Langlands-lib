/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Trace.TraceBaseChangeFirst
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Trace.TraceBaseChangeFirst
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
import WeilConjectures.CategoryTheory.Projection.ProjectionMateSquareCoherence
/-! # Forward projection and exchange for the native self-square

The tensor comparison is stored once before specializing the adjunction mate calculation.
(blueprint: lem-sfb-native-forward-self-square-projection). -/

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
universe u u₁ u₂ u₃

attribute [local instance 20000]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
  AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
attribute [local irreducible] DerivedCategory.braidedCategory' NatTrans.vcomp
attribute [local irreducible] DerivedCategory.Qh
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.leftDerivedTensorComparison CategoryTheory.Functor.leftDerivedFunctorCounit
  CategoryTheory.Mod.monoidalClosed CategoryTheory.Sheaf.monObj_sheafCompose_obj
  AlgebraicGeometry.ProEtale.upperStarFromPoint

namespace CategoryTheory

/-- The forward projection square with its tensor structures stored once.
Source: the projection/exchange compatibility in the Second identity
(blueprint: lem-sfb-native-forward-self-square-projection). -/
def ForwardProjectionSquare
    {C D V : Type*} [Category C] [Category D] [Category V]
    {F : C ⥤ D} {U₁ U₂ : D ⥤ V} (d : TraceComparisonData F U₁ U₂)
    (P : D ⥤ C) (Q : V ⥤ D) (a : F ⊣ P) (a₂ : U₂ ⊣ Q)
    (s : F ⋙ U₂ ≅ F ⋙ U₁) : Prop :=
  letI := d.monoidalC
  letI := d.monoidalD
  letI := d.monoidalV
  ∀ (K : C) (T : D),
    F.map (traceProjectionFromComparison a d.tensorF K T) ≫
      (traceAbstractMate a a₂ s).app (F.obj K ⊗ T) ≫
      Q.map (d.tensorOne (F.obj K) T ≫ tensorHom (s.inv.app K) (𝟙 (U₁.obj T))) =
    d.tensorF K (P.obj T) ≫ (F.obj K ◁ (traceAbstractMate a a₂ s).app T) ≫
      traceProjectionFromComparison a₂ d.tensorTwo (F.obj K) (U₁.obj T)

-- Retain only the fields used by the forward equation when changing tensor interfaces.
private structure ForwardTensorData
    {C D V : Type*} [Category C] [Category D] [Category V]
    (F : C ⥤ D) (U₁ U₂ : D ⥤ V) where
  [monoidalC : MonoidalCategory C]
  [monoidalD : MonoidalCategory D]
  [monoidalV : MonoidalCategory V]
  tensorF : ∀ K M : C, F.obj (K ⊗ M) ⟶ F.obj K ⊗ F.obj M
  tensorOne : ∀ K M : D, U₁.obj (K ⊗ M) ⟶ U₁.obj K ⊗ U₁.obj M
  tensorTwo : ∀ K M : D, U₂.obj (K ⊗ M) ⟶ U₂.obj K ⊗ U₂.obj M

private def forgetForwardTensorData
    {C D V : Type*} [Category C] [Category D] [Category V]
    {F : C ⥤ D} {U₁ U₂ : D ⥤ V} (d : TraceComparisonData F U₁ U₂) :
    ForwardTensorData F U₁ U₂ where
  monoidalC := d.monoidalC
  monoidalD := d.monoidalD
  monoidalV := d.monoidalV
  tensorF := d.tensorF
  tensorOne := d.tensorOne
  tensorTwo := d.tensorTwo

private theorem forward_tensor_data_ext
    {C D V : Type*} [Category C] [Category D] [Category V]
    {F : C ⥤ D} {U₁ U₂ : D ⥤ V} (d e : ForwardTensorData F U₁ U₂)
    (hc : d.monoidalC = e.monoidalC) (hd : d.monoidalD = e.monoidalD)
    (hv : d.monoidalV = e.monoidalV)
    (hf : ∀ K T, HEq (d.tensorF K T) (e.tensorF K T))
    (h₁ : ∀ K T, HEq (d.tensorOne K T) (e.tensorOne K T))
    (h₂ : ∀ K T, HEq (d.tensorTwo K T) (e.tensorTwo K T)) : d = e := by
  cases d with
  | @mk mc md mv df d₁ d₂ =>
    cases e with
    | @mk nc nd nv ef e₁ e₂ =>
      dsimp only at hc hd hv hf h₁ h₂
      cases hc
      cases hd
      cases hv
      have hf' : df = ef := by
        funext K T
        exact eq_of_heq (hf K T)
      have h₁' : d₁ = e₁ := by
        funext K T
        exact eq_of_heq (h₁ K T)
      have h₂' : d₂ = e₂ := by
        funext K T
        exact eq_of_heq (h₂ K T)
      cases hf'
      cases h₁'
      cases h₂'
      rfl

private def forwardProjectionF
    {C D V : Type*} [Category C] [Category D] [Category V]
    {F : C ⥤ D} {U₁ U₂ : D ⥤ V} (d : ForwardTensorData F U₁ U₂)
    {P : D ⥤ C} (a : F ⊣ P) (K : C) (T : D) :=
  letI := d.monoidalC
  letI := d.monoidalD
  traceProjectionFromComparison a d.tensorF K T

private def forwardProjectionTwo
    {C D V : Type*} [Category C] [Category D] [Category V]
    {F : C ⥤ D} {U₁ U₂ : D ⥤ V} (d : ForwardTensorData F U₁ U₂)
    {Q : V ⥤ D} (a : U₂ ⊣ Q) (K : D) (T : V) :=
  letI := d.monoidalD
  letI := d.monoidalV
  traceProjectionFromComparison a d.tensorTwo K T

private def ForwardTensorSquare
    {C D V : Type*} [Category C] [Category D] [Category V]
    {F : C ⥤ D} {U₁ U₂ : D ⥤ V} (d : ForwardTensorData F U₁ U₂)
    (P : D ⥤ C) (Q : V ⥤ D) (a : F ⊣ P) (a₂ : U₂ ⊣ Q)
    (s : F ⋙ U₂ ≅ F ⋙ U₁) : Prop :=
  letI := d.monoidalC
  letI := d.monoidalD
  letI := d.monoidalV
  ∀ (K : C) (T : D),
    F.map (forwardProjectionF d a K T) ≫
      (traceAbstractMate a a₂ s).app (F.obj K ⊗ T) ≫
      Q.map (d.tensorOne (F.obj K) T ≫ tensorHom (s.inv.app K) (𝟙 (U₁.obj T))) =
    d.tensorF K (P.obj T) ≫ (F.obj K ◁ (traceAbstractMate a a₂ s).app T) ≫
      forwardProjectionTwo d a₂ (F.obj K) (U₁.obj T)

private theorem forward_tensor_of_trace
    {C D V : Type*} [Category C] [Category D] [Category V]
    {F : C ⥤ D} {U₁ U₂ : D ⥤ V} (d : TraceComparisonData F U₁ U₂)
    (P : D ⥤ C) (Q : V ⥤ D) (a : F ⊣ P) (a₂ : U₂ ⊣ Q)
    (s : F ⋙ U₂ ≅ F ⋙ U₁) (h : ForwardProjectionSquare d P Q a a₂ s) :
    ForwardTensorSquare (forgetForwardTensorData d) P Q a a₂ s := by
  exact h

private theorem forward_tensor_transport
    {C D V : Type*} [Category C] [Category D] [Category V]
    {F : C ⥤ D} {U₁ U₂ : D ⥤ V}
    (d e : TraceComparisonData F U₁ U₂) (t : ForwardTensorData F U₁ U₂)
    (he : d = e) (ht : forgetForwardTensorData e = t)
    (P : D ⥤ C) (Q : V ⥤ D) (a : F ⊣ P) (a₂ : U₂ ⊣ Q)
    (s : F ⋙ U₂ ≅ F ⋙ U₁) (h : ForwardProjectionSquare d P Q a a₂ s) :
    ForwardTensorSquare t P Q a a₂ s := by
  cases he
  cases ht
  exact forward_tensor_of_trace d P Q a a₂ s h

private theorem forward_tensor_component
    {C D V : Type*} [Category C] [Category D] [Category V]
    [mc : MonoidalCategory C] [md : MonoidalCategory D] [mv : MonoidalCategory V]
    {F : C ⥤ D} {U₁ U₂ : D ⥤ V}
    (dF : ∀ A B, F.obj (A ⊗ B) ⟶ F.obj A ⊗ F.obj B)
    (d₁ : ∀ A B, U₁.obj (A ⊗ B) ⟶ U₁.obj A ⊗ U₁.obj B)
    (d₂ : ∀ A B, U₂.obj (A ⊗ B) ⟶ U₂.obj A ⊗ U₂.obj B)
    (P : D ⥤ C) (Q : V ⥤ D) (a : F ⊣ P) (b : U₂ ⊣ Q)
    (s : F ⋙ U₂ ≅ F ⋙ U₁)
    (h : ForwardTensorSquare
      { monoidalC := mc, monoidalD := md, monoidalV := mv,
        tensorF := dF, tensorOne := d₁, tensorTwo := d₂ } P Q a b s)
    (K : C) (T : D) :
    F.map (traceProjectionFromComparison a dF K T) ≫
      (traceAbstractMate a b s).app (F.obj K ⊗ T) ≫
      Q.map (d₁ (F.obj K) T ≫ tensorHom (s.inv.app K) (𝟙 (U₁.obj T))) =
      dF K (P.obj T) ≫ (F.obj K ◁ (traceAbstractMate a b s).app T) ≫
        traceProjectionFromComparison b d₂ (F.obj K) (U₁.obj T) := by
  exact h K T

end CategoryTheory

/-- The canonical derived tensor comparison for a functor between internal-module categories.
Source: the canonical derived tensor comparison
(blueprint: lem-sfb-native-forward-self-square-projection). -/
def CategoryTheory.moduleDerivedTensorComparisonHom
    {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [SymmetricCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [SymmetricCategory D] [MonoidalPreadditive D] [MonoidalClosed D]
    [Abelian.HasFunctorialFlatResolution D]
    (RC : C) [MonObj RC] [hRCc : IsCommMonObj RC]
    (RD : D) [MonObj RD] [hRDc : IsCommMonObj RD]
    (F : Mod C RC ⥤ Mod D RD) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [hFflat : F.PreservesFlat] [F.IsLeftAdjoint] [hFmon : F.Monoidal]
    (K T : DerivedCategory (Mod C RC)) :=
  (F.leftDerivedTensorComparison.app K).app T

private theorem module_tensorF_heq
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
    (K T : DerivedCategory (Mod C RC)) :
    HEq ((forgetForwardTensorData
      (moduleTraceComparisonData RC RD RV F U₁ U₂)).tensorF K T)
      (CategoryTheory.moduleDerivedTensorComparisonHom RC RD F K T) := by
  rfl

private theorem module_tensorOne_heq
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
    (K T : DerivedCategory (Mod D RD)) :
    HEq ((forgetForwardTensorData
      (moduleTraceComparisonData RC RD RV F U₁ U₂)).tensorOne K T)
      (CategoryTheory.moduleDerivedTensorComparisonHom RD RV U₁ K T) := by
  rfl

private theorem module_tensorTwo_heq
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
    (K T : DerivedCategory (Mod D RD)) :
    HEq ((forgetForwardTensorData
      (moduleTraceComparisonData RC RD RV F U₁ U₂)).tensorTwo K T)
      (CategoryTheory.moduleDerivedTensorComparisonHom RD RV U₂ K T) := by
  rfl

attribute [local irreducible] ForwardProjectionSquare
attribute [local implicit_reducible] derivedTraceComparisonData
  moduleTraceComparisonData traceNativeComparisonData

private theorem derived_projection_square
    {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [SymmetricCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [SymmetricCategory D] [MonoidalPreadditive D] [MonoidalClosed D]
    [Abelian.HasFunctorialFlatResolution D]
    {V : Type u₃} [Category.{u + 1} V] [Abelian V] [IsGrothendieckAbelian.{u + 1} V]
    [MonoidalCategory V] [SymmetricCategory V] [MonoidalPreadditive V] [MonoidalClosed V]
    [Abelian.HasFunctorialFlatResolution V]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
    (U₁ U₂ : D ⥤ V)
    [U₁.Additive] [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
    [U₁.PreservesFlat] [U₁.IsLeftAdjoint] [U₁.Monoidal]
    [U₂.Additive] [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
    [U₂.PreservesFlat] [U₂.IsLeftAdjoint] [U₂.Monoidal]
    (P : DerivedCategory D ⥤ DerivedCategory C)
    (Q : DerivedCategory V ⥤ DerivedCategory D)
    (a : F.leftDerivedFunctor ⊣ P) (a₂ : U₂.leftDerivedFunctor ⊣ Q)
    (s : F.leftDerivedFunctor ⋙ U₂.leftDerivedFunctor ≅
      F.leftDerivedFunctor ⋙ U₁.leftDerivedFunctor)
    (hs : traceDataSquare (derivedTraceComparisonData F U₁ U₂) s) :
    ForwardProjectionSquare (derivedTraceComparisonData F U₁ U₂) P Q a a₂ s := by
  unfold ForwardProjectionSquare
  dsimp only [traceDataSquare, derivedTraceComparisonData] at hs ⊢
  intro K T
  unfold traceProjectionFromComparison traceAbstractMate
  simp only [id_tensorHom]
  let TC := CategoryTheory.Prod.swap (DerivedCategory C) (DerivedCategory C) ⋙
    tensor (DerivedCategory C)
  let TD := CategoryTheory.Prod.swap (DerivedCategory D) (DerivedCategory D) ⋙
    tensor (DerivedCategory D)
  let TV := CategoryTheory.Prod.swap (DerivedCategory V) (DerivedCategory V) ⋙
    tensor (DerivedCategory V)
  let dF : TC ⋙ F.leftDerivedFunctor ⟶
      (F.leftDerivedFunctor.prod F.leftDerivedFunctor) ⋙ TD := {
    app := fun Z ↦ (F.leftDerivedTensorComparison.app Z.2).app Z.1
    naturality := fun X Y f ↦
      F.leftDerivedTensorComparison_naturality_tensorHom f.2 f.1 }
  let d₁ : TD ⋙ U₁.leftDerivedFunctor ⟶
      (U₁.leftDerivedFunctor.prod U₁.leftDerivedFunctor) ⋙ TV := {
    app := fun Z ↦ (U₁.leftDerivedTensorComparison.app Z.2).app Z.1
    naturality := fun X Y f ↦
      U₁.leftDerivedTensorComparison_naturality_tensorHom f.2 f.1 }
  let d₂ : TD ⋙ U₂.leftDerivedFunctor ⟶
      (U₂.leftDerivedFunctor.prod U₂.leftDerivedFunctor) ⋙ TV := {
    app := fun Z ↦ (U₂.leftDerivedTensorComparison.app Z.2).app Z.1
    naturality := fun X Y f ↦
      U₂.leftDerivedTensorComparison_naturality_tensorHom f.2 f.1 }
  simpa only [TC, TD, TV, dF, d₁, d₂, tensor, CategoryTheory.Prod.swap,
    traceProjectionFromComparison, traceAbstractMate, Functor.comp_obj, Functor.comp_map,
    Functor.prod_obj, Functor.prod_map, Functor.id_obj, id_tensorHom] using
    projectionMate_square_of_tensor_coherence a a₂ TC TD TD TV dF dF d₁ d₂ s
      (fun M N ↦ hs N M) T K

private theorem module_projection_square
    {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [SymmetricCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [SymmetricCategory D] [MonoidalPreadditive D] [MonoidalClosed D]
    [Abelian.HasFunctorialFlatResolution D]
    {V : Type u₃} [Category.{u + 1} V] [Abelian V] [IsGrothendieckAbelian.{u + 1} V]
    [MonoidalCategory V] [SymmetricCategory V] [MonoidalPreadditive V] [MonoidalClosed V]
    [Abelian.HasFunctorialFlatResolution V]
    (RC : C) [MonObj RC] [IsCommMonObj RC]
    (RD : D) [MonObj RD] [IsCommMonObj RD]
    (RV : V) [MonObj RV] [IsCommMonObj RV]
    (F : Mod C RC ⥤ Mod D RD) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
    (U₁ U₂ : Mod D RD ⥤ Mod V RV)
    [U₁.Additive] [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
    [U₁.PreservesFlat] [U₁.IsLeftAdjoint] [U₁.Monoidal]
    [U₂.Additive] [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
    [U₂.PreservesFlat] [U₂.IsLeftAdjoint] [U₂.Monoidal]
    (P : DerivedCategory (Mod D RD) ⥤ DerivedCategory (Mod C RC))
    (Q : DerivedCategory (Mod V RV) ⥤ DerivedCategory (Mod D RD))
    (a : F.leftDerivedFunctor ⊣ P) (a₂ : U₂.leftDerivedFunctor ⊣ Q)
    (s : F.leftDerivedFunctor ⋙ U₂.leftDerivedFunctor ≅
      F.leftDerivedFunctor ⋙ U₁.leftDerivedFunctor)
    (hs : traceDataSquare (moduleTraceComparisonData RC RD RV F U₁ U₂) s) :
    ForwardProjectionSquare (moduleTraceComparisonData RC RD RV F U₁ U₂) P Q a a₂ s := by
  exact derived_projection_square F U₁ U₂ P Q a a₂ s hs

namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local instance 20000] CategoryTheory.traceSheafSymmetric
attribute [local instance 20000] projectionCoefficientMonObj projectionSheafMonoidal
  projectionModuleCategory
attribute [local instance 20000] traceModuleGrothendieck traceModuleFlat
  traceTensorLeft traceTensorRight traceGradedTensor traceGradedTensorLeft
  traceGradedTensorRight traceGradedTensorFour
attribute [local irreducible] upperStar lowerStar
  CategoryTheory.Functor.rightDerivedFunctor

/-- The forward projection square for the canonical pullback square and its mate.
Source: rational projective-line triangle, Second identity, extraction of q*K;
Stacks 07A7 and 0D6D (blueprint: lem-sfb-native-forward-self-square-projection).

Proof: the canonical pullback composition comparison preserves the derived tensor
comparison. Apply the adjunction mate square with both tensor variables reversed.
This uses only the tensor comparison and the unit/counit triangle identities; no
projection or exchange map is assumed invertible. -/
theorem native_forward_self_square_projection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y W : Scheme.{u}}
    (f : X ⟶ Y) (p q : W ⟶ X) (w : p ≫ f = q ≫ f) :
    ForwardProjectionSquare (traceNativeComparisonData Λ f p q)
      (tracePush Λ f) (tracePush Λ q) (traceAdjunction Λ f) (traceAdjunction Λ q)
      (tracePullSquare Λ f p q w) := by
  unfold traceNativeComparisonData
  exact module_projection_square (condensedRingObj Λ Y) (condensedRingObj Λ X)
    (condensedRingObj Λ W) (upperStar Λ f) (upperStar Λ p) (upperStar Λ q)
    (tracePush Λ f) (tracePush Λ q) (traceAdjunction Λ f) (traceAdjunction Λ q)
    (tracePullSquare Λ f p q w) (trace_square_tensor Λ f p q w)

end AlgebraicGeometry.ProEtale.CondensedRing
