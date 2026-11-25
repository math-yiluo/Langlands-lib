/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Ambient.RationalP1AmbientComposites
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitInversionCondition
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1CounitInversionCondition
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTatePullback
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTrace
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalTowerCoefficients
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1DiagonalTensor
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.TateTwistedProjection
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalComposition
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ProEtaleProjectionExchangeMaps

import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1LocalizingPreservation
import all WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveNormalizedUnitCounitRestriction
import all WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1LocalizingProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.UnboundedBaseChangeExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeAdmissibleGenerators
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1LineFromPreservation
import Mathlib.CategoryTheory.ObjectProperty.Shift
import Mathlib.CategoryTheory.Triangulated.Subcategory

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-! # The specified rational projective-line unit and counit
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] unitComponent counitComponent twistProjectionMap
attribute [local irreducible] coefficient line diagram secondLineComparison
attribute [local irreducible] firstProjection secondProjection square condensedAmbientExchange
attribute [local irreducible] tensorShiftIso twist rationalTwistFunctor projectionMateMap
  AlgebraicGeometry.ProEtale.RationalP1.projectionMap
  pushSectionIso supportedUnitIso singleUnitIso trace

section InversionHelpers

attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  CondensedRing.upperStar CondensedRing.lowerStar

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Cache the canonical exchange proposition before coefficient specialization. -/
@[irreducible] private def unitExchangeInversion (Y : Scheme.{u})
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) : Prop :=
  IsIso ((condensedAmbientExchange Λ (square Y)).app M)

/-- Cache the native right projection proposition before coefficient specialization. -/
@[irreducible] private def unitNativeMateInversion (Y : Scheme.{u})
    (L : ∀ Z : Scheme.{u}, Modules Λ Z)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) : Prop :=
  IsIso (moduleObjectProjectionMate Λ (secondProjection Y)
    ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)
    (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
      (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧))

attribute [-instance] internalMonoidal internalTensorCommShift in
private theorem normalized_mate_isIso
    (a : ProjectionMateFamily Λ) (ha : ProjectionMateNormalized Λ a)
    {X S : Scheme.{u}} (f : X ⟶ S)
    (A : DerivedCategory (Modules Λ X)) (B : DerivedCategory (Modules Λ S))
    (h : IsIso (moduleObjectProjectionMate Λ f A B)) : IsIso (a f A B) := by
  unfold ProjectionMateNormalized ProjectionMateFamily internalMonoidal
    internalTensorBundle nativeTensorBundle at *
  dsimp only at ha
  rw [eq_of_heq (ha f A B)]
  exact h

private theorem selected_mate_isIso {X S : Scheme.{u}} (f : X ⟶ S)
    (A : DerivedCategory (Modules Λ X)) (B : DerivedCategory (Modules Λ S))
    (h : IsIso (moduleObjectProjectionMate Λ f A B)) :
    IsIso (projectionMateMap Λ f A B) := by
  unfold projectionMateMap
  exact normalized_mate_isIso Λ (projectionMate_existsUnique Λ).exists.choose
    (projectionMate_existsUnique Λ).exists.choose_spec f A B h

private theorem unit_condition_of_native (Y : Scheme.{u})
    (L : ∀ Z : Scheme.{u}, Modules Λ Z)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (hb : unitExchangeInversion Λ Y M) (hp : unitNativeMateInversion Λ Y L M) :
    ∀ e, UnitInversionCondition Λ Y L e M := by
  intro e
  unfold unitExchangeInversion at hb
  unfold unitNativeMateInversion at hp
  have := selected_mate_isIso Λ (secondProjection Y)
    ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M) _ hp
  refine ⟨hb, ?_⟩
  unfold twistProjectionMap
  infer_instance

private theorem termwise_exchange_isIso_iff
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    (A : DerivedCategory (Modules Λ X)) :
    IsIso ((termwiseCondensedAmbientExchange Λ sq).app A) ↔
      IsIso ((condensedAmbientExchange Λ sq).app A) := by
  simp only [termwiseCondensedAmbientExchange, NatTrans.comp_app,
    isIso_comp_left_iff, isIso_comp_right_iff]

private theorem exchange_isIso_of_extension
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    (he : UnboundedBaseChangeExtension Λ sq)
    (hgen : ∀ A, (constantModelBoundedConstructible Λ X A ∧
      _root_.DerivedCategory.finiteTorAmplitude _ A) →
        IsIso ((condensedAmbientExchange Λ sq).app A))
    (A : DerivedCategory (Modules Λ X)) (hA : localizingClosureProEtale Λ X A) :
    IsIso ((condensedAmbientExchange Λ sq).app A) := by
  exact (termwise_exchange_isIso_iff Λ sq A).1
    (he (fun B hB ↦ (termwise_exchange_isIso_iff Λ sq B).2 (hgen B hB)) A hA)

private theorem coefficient_admissible
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l)) :
    IsLocalizingAdmissibleCoefficient l (coefficient l c).X := by
  cases c with
  | none =>
    unfold coefficient
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))))
  | some E =>
    unfold coefficient
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩)))

private theorem rational_coefficient_closure_eq
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (Z : Scheme.{u}) [CompactSpace Z] [QuasiSeparatedSpace Z] :
    localizingClosureProEtale (coefficient l c).X Z =
      CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (coefficient l c).X Z) := by
  apply (localizingClosure_ctf_equals_bc l Z (coefficient l c).X ?_).1.2.2.2.1
  cases c with
  | none =>
    unfold coefficient
    exact Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))
  | some E =>
    unfold coefficient
    exact Or.inr (Or.inr (Or.inl ⟨E, Or.inr ⟨Iso.refl _⟩⟩))

private theorem coefficient_extension
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {X' X Y' Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
    [IsSeparated (X' ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))]
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]
    [IsProper f] (sq : ChosenCartesianSquare g' f' f g) :
    UnboundedBaseChangeExtension (coefficient l c).X sq := by
  cases c with
  | none =>
    unfold coefficient
    exact (unboundedBaseChangeExtension l k sq).2.2.2.2
  | some E =>
    unfold coefficient
    exact ((unboundedBaseChangeExtension l k sq).2.2.2.1 E).2

end InversionHelpers

attribute [local irreducible] UnitComponentNormalized CounitComponentNormalized

variable (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
  (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
  (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]

-- Keep fixed site and derived comparisons folded during elaboration.
include k p hpl in
/-- The actual two functors preserve Loc of finite-constant-model Dbc. -/
theorem localizingPreservation :
    (∀ M, CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (coefficient l c).X (ProjectiveLine Y)) M →
      CategoryTheory.localizingClosure (constantModelBoundedConstructible (coefficient l c).X Y)
        ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M)) ∧
    (∀ K, CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (coefficient l c).X Y) K →
      CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (coefficient l c).X (ProjectiveLine Y))
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y) ⋙
          twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj K)) := by
  have h := localizingPreservationChecks l c k p hpl Y
  exact ⟨h.pushQ.preserves, h.twistedPullQ.preserves⟩

-- Keep fixed site and derived comparisons folded during elaboration.
/-- The restriction of the actual direct image, with the inherited full Hom sets. -/
def push : rationalLocalizingCategory (coefficient l c).X (ProjectiveLine Y) ⥤
    rationalLocalizingCategory (coefficient l c).X Y :=
  (CategoryTheory.localizingClosure
    (constantModelBoundedConstructible (coefficient l c).X Y)).lift
    ((rationalLocalizingInclusion (coefficient l c).X (ProjectiveLine Y)) ⋙
      moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y))
    (fun M ↦ (localizingPreservation l c k p hpl Y).1 M.obj M.property)

-- Keep fixed site and derived comparisons folded during elaboration.
/-- Pullback followed by the positive Tate twist and shift two, restricted to Loc(Dbc). -/
def exceptional : rationalLocalizingCategory (coefficient l c).X Y ⥤
    rationalLocalizingCategory (coefficient l c).X (ProjectiveLine Y) :=
  (CategoryTheory.localizingClosure
    (constantModelBoundedConstructible (coefficient l c).X (ProjectiveLine Y))).lift
    ((rationalLocalizingInclusion (coefficient l c).X Y) ⋙
      moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y) ⋙
        twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y)))
    (fun K ↦ (localizingPreservation l c k p hpl Y).2 K.obj K.property)

-- Keep fixed site and derived comparisons folded during elaboration.
/-- The type of the two natural transformations, before asserting any triangles. -/
def UnitCounitType : Type (u + 2) :=
  (𝟭 _ ⟶ push l c k p hpl Y ⋙ exceptional l c k p hpl Y) ×
    (exceptional l c k p hpl Y ⋙ push l c k p hpl Y ⟶ 𝟭 _)

include k p hpl in
private theorem unit_exchange_isIso
    (M : rationalLocalizingCategory (coefficient l c).X (ProjectiveLine Y)) :
    unitExchangeInversion (coefficient l c).X Y M.obj := by
  unfold unitExchangeInversion
  have : Fact (ringChar k).Prime := ⟨by rw [ringChar.eq k p]; exact Fact.out⟩
  have : Fact (ringChar k ≠ l) := ⟨by rw [ringChar.eq k p]; exact hpl⟩
  have h := localizingPreservationChecks l c k p hpl Y
  have := h.geometry.qcqsY.1
  have := h.geometry.qcqsY.2
  have := h.geometry.qcqsP.1
  have := h.geometry.qcqsP.2
  have := h.geometry.qcqsW.1
  have := h.geometry.qcqsW.2
  have := h.geometry.properSecond
  let : (ProjectiveLine Y).Over (Spec (.of k)) :=
    ⟨(ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))⟩
  let : (diagonalSurface Y).Over (Spec (.of k)) :=
    ⟨firstProjection Y ≫ (ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))⟩
  have : LocallyOfFiniteType (ProjectiveLine Y ↘ Spec (.of k)) := h.geometry.standingP.2.1
  have : QuasiCompact (ProjectiveLine Y ↘ Spec (.of k)) := h.geometry.standingP.2.2
  have : IsSeparated (ProjectiveLine Y ↘ Spec (.of k)) := h.geometry.standingP.1
  have : LocallyOfFiniteType (diagonalSurface Y ↘ Spec (.of k)) := h.geometry.standingW.2.1
  have : QuasiCompact (diagonalSurface Y ↘ Spec (.of k)) := h.geometry.standingW.2.2
  have : IsSeparated (diagonalSurface Y ↘ Spec (.of k)) := h.geometry.standingW.1
  have : (ProjectiveLine Y ↘ Y).IsOver (Spec (.of k)) := ⟨rfl⟩
  have : (firstProjection Y).IsOver (Spec (.of k)) := ⟨rfl⟩
  have : (secondProjection Y).IsOver (Spec (.of k)) := by
    constructor
    change secondProjection Y ≫ ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) =
      firstProjection Y ≫ ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k)))
    unfold firstProjection secondProjection
    simpa only [Category.assoc] using
      congrArg (fun f : diagonalSurface Y ⟶ Y ↦ f ≫ (Y ↘ Spec (.of k)))
        (pullback.condition (f := ProjectiveLine Y ↘ Y) (g := ProjectiveLine Y ↘ Y)).symm
  have hc := coefficient_admissible l c
  have hExt := coefficient_extension l c k (square Y)
  have hclosure := rational_coefficient_closure_eq l c (ProjectiveLine Y)
  have hb : IsIso ((condensedAmbientExchange (coefficient l c).X (square Y)).app M.obj) := by
    apply exchange_isIso_of_extension (coefficient l c).X (square Y) hExt
    · intro A hA
      exact properBaseChange_admissible_generators l (coefficient l c).X hc k
        (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) (square Y) A hA
    · rw [hclosure]
      exact M.property
  exact hb

include k p hpl in
private theorem unit_mate_isIso
    (M : rationalLocalizingCategory (coefficient l c).X (ProjectiveLine Y)) :
    unitNativeMateInversion (coefficient l c).X Y (line l c) M.obj := by
  unfold unitNativeMateInversion
  have : Fact (ringChar k).Prime := ⟨by rw [ringChar.eq k p]; exact Fact.out⟩
  have : Fact (ringChar k ≠ l) := ⟨by rw [ringChar.eq k p]; exact hpl⟩
  have h := localizingPreservationChecks l c k p hpl Y
  have := h.geometry.qcqsY.1
  have := h.geometry.qcqsY.2
  have := h.geometry.qcqsP.1
  have := h.geometry.qcqsP.2
  have := h.geometry.qcqsW.1
  have := h.geometry.qcqsW.2
  have := h.geometry.properSecond
  let : (ProjectiveLine Y).Over (Spec (.of k)) :=
    ⟨(ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))⟩
  let : (diagonalSurface Y).Over (Spec (.of k)) :=
    ⟨firstProjection Y ≫ (ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))⟩
  have : LocallyOfFiniteType (ProjectiveLine Y ↘ Spec (.of k)) := h.geometry.standingP.2.1
  have : QuasiCompact (ProjectiveLine Y ↘ Spec (.of k)) := h.geometry.standingP.2.2
  have : IsSeparated (ProjectiveLine Y ↘ Spec (.of k)) := h.geometry.standingP.1
  have : LocallyOfFiniteType (diagonalSurface Y ↘ Spec (.of k)) := h.geometry.standingW.2.1
  have : QuasiCompact (diagonalSurface Y ↘ Spec (.of k)) := h.geometry.standingW.2.2
  have : IsSeparated (diagonalSurface Y ↘ Spec (.of k)) := h.geometry.standingW.1
  have : (ProjectiveLine Y ↘ Y).IsOver (Spec (.of k)) := ⟨rfl⟩
  have : (firstProjection Y).IsOver (Spec (.of k)) := ⟨rfl⟩
  have : (secondProjection Y).IsOver (Spec (.of k)) := by
    constructor
    change secondProjection Y ≫ ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) =
      firstProjection Y ≫ ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k)))
    unfold firstProjection secondProjection
    simpa only [Category.assoc] using
      congrArg (fun f : diagonalSurface Y ⟶ Y ↦ f ≫ (Y ↘ Spec (.of k)))
        (pullback.condition (f := ProjectiveLine Y ↘ Y) (g := ProjectiveLine Y ↘ Y)).symm
  have hloc := (localizingClosure_exists (coefficient l c).X (ProjectiveLine Y)
    (constantModelBoundedConstructible (coefficient l c).X (ProjectiveLine Y))).2.2.2
  have := hloc.1.1
  have hline := ObjectProperty.le_shift
    (CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (coefficient l c).X (ProjectiveLine Y))) (2 : ℤ) _
    (hloc.2.1 _ h.objectsP.positiveLine)
  exact selected_projection_isIso l c k p hpl (secondProjection Y) _ _
    (h.pullFirst.preserves M.obj M.property) hline

-- Keep fixed site and derived comparisons folded during elaboration.
/-- Invertibility of precisely the exchange and twisted projection in the unit formula. -/
theorem unitInversions (M : rationalLocalizingCategory (coefficient l c).X (ProjectiveLine Y)) :
    UnitInversionCondition (coefficient l c).X Y (line l c)
      (secondLineComparison l c k p hpl Y) M.obj := by
  exact unit_condition_of_native (coefficient l c).X Y (line l c) M.obj
    (unit_exchange_isIso l c k p hpl Y M) (unit_mate_isIso l c k p hpl Y M)
    (secondLineComparison l c k p hpl Y)

-- Keep fixed site and derived comparisons folded during elaboration.
include k p hpl in
/-- Invertibility of precisely the projection appearing in the counit. -/
theorem counitInversion (K : rationalLocalizingCategory (coefficient l c).X Y) :
    CounitInversionCondition (coefficient l c).X Y (line l c) K.obj := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  have hL := line_localizing_of_preservation (coefficient l c).X
    (ProjectiveLine Y ↘ Y) (line l c (ProjectiveLine Y))
    (localizingPreservation l c k p hpl Y).2
  have : LocallyOfFiniteType (ProjectiveLine Y ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))))
  have : QuasiCompact (ProjectiveLine Y ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))))
  have : IsSeparated (ProjectiveLine Y ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))))
  have : (ProjectiveLine Y ↘ Y).IsOver (Spec (.of k)) := ⟨rfl⟩
  unfold CounitInversionCondition
  exact projectionMap_isIso_localizing l c k p hpl (ProjectiveLine Y ↘ Y)
    K.obj _ K.property hL

-- Keep fixed site and derived comparisons folded during elaboration.
/-- Componentwise normalization by the actual canonical ambient formulas. -/
def UnitCounitNormalized (family : Family l Y) (a : UnitCounitType l c k p hpl Y) : Prop :=
  (∀ M : rationalLocalizingCategory (coefficient l c).X (ProjectiveLine Y),
    UnitComponentNormalized (coefficient l c).X Y (line l c) (diagram l c Y family)
      (secondLineComparison l c k p hpl Y) M.obj (a.1.app M).hom) ∧
  (∀ K : rationalLocalizingCategory (coefficient l c).X Y,
    CounitComponentNormalized (coefficient l c).X Y (line l c) (diagram l c Y family)
      K.obj (a.2.app K).hom)

-- Keep fixed site and derived comparisons folded during elaboration.
/-- The fixed formulas form a unique pair of natural transformations. -/
theorem unitCounit_existsUnique (family : Family l Y) :
    ∃! a : UnitCounitType l c k p hpl Y, UnitCounitNormalized l c k p hpl Y family a := by
  exact restrictedUnitCounit_existsUnique (coefficient l c).X Y (line l c)
    (diagram l c Y family) (secondLineComparison l c k p hpl Y) _ _
    (fun M ↦ (localizingPreservation l c k p hpl Y).1 M.obj M.property)
    (fun K ↦ (localizingPreservation l c k p hpl Y).2 K.obj K.property)
    (unitInversions l c k p hpl Y) (counitInversion l c k p hpl Y)
    (push l c k p hpl Y) (exceptional l c k p hpl Y)
    (by unfold push; rfl) (by unfold exceptional; rfl)

-- Keep fixed site and derived comparisons folded during elaboration.
/-- The uniquely normalized diagonal unit and trace counit; no adjunction is assumed. -/
def unitCounit (family : Family l Y) : UnitCounitType l c k p hpl Y :=
  (unitCounit_existsUnique l c k p hpl Y family).exists.choose

/- STATEMENT-DISPUTED: The theorem quantifies over arbitrary `Functor.CommShift`
structures.  Those structures contain chosen isomorphism data and are not
subsingleton; rescaling one comparison by a nontrivial scalar changes the
required natural-transformation square.  Therefore the stated universal claim
cannot be proved without fixing the canonical shift structures. -/

end AlgebraicGeometry.ProEtale.RationalP1
