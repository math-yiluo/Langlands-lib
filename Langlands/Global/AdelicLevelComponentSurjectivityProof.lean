import Langlands.AlgebraicGeometry.UniformLangWeilComponentLiftingProof
import Langlands.Global.AdelicLevelComponentSurjectivityStatement
import Langlands.Global.CompletionIntegersSmoothPointLifting
import Langlands.Global.CompletionResidueBounds
import Langlands.Global.FunctionFieldAdelesLocallyCompactProof

/-! # Actual integral lifts outside a finite set of global places -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology

/-- Uniform exact integral lifts at all actual curve places outside one
finite set. The original coefficient algebra may be supplied separately
at each place where an integral lift is requested. -/
def curvePlaceComponentAlmostAllIntegralPointLifts
    (hLW : UniformLangWeilStatement.{u})
    (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (C : Type u) [CommRing C] (B Y : Over (Spec (CommRingCat.of C)))
    (f : Y ⟶ B)
    (hBft : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from B.left))
    (hBqc : CompactSpace B.left) (hsmooth : Smooth f.left)
    (hsep : _root_.AlgebraicGeometry.IsSeparated f.left) (hqc : QuasiCompact f.left)
    (hconn : GeometricallyConnected f.left) :
    Σ S : Finset (AlgebraicCurve.Place k F),
      (v : AlgebraicCurve.Place k F) → v ∉ S →
        [Algebra C (curvePlaceCompletionIntegers v)] →
        (p : RingPoint C B (curvePlaceCompletionIntegers v)) →
        {a : RingPoint C Y (curvePlaceCompletionIntegers v) // a ≫ f = p} := by
  let lifts := uniformLangWeilComponentHenselianRingPointLifts hLW C B Y f
    hBft hBqc hsmooth hsep hqc hconn
  refine ⟨curvePlaceSmallCompletionResiduePlaces k F (lifts.1.1 ^ 2),
    fun v hv _ p => ?_⟩
  let : HenselianLocalRing (curvePlaceCompletionIntegers v) :=
    curvePlaceCompletionIntegers_henselian v
  let : Finite (IsLocalRing.ResidueField (curvePlaceCompletionIntegers v)) :=
    curvePlaceCompletionResidue_finite k F v
  exact lifts.2 (curvePlaceCompletionIntegers v)
    (IsLocalRing.ResidueField (curvePlaceCompletionIntegers v))
    (IsScalarTower.toAlgHom C (curvePlaceCompletionIntegers v)
      (IsLocalRing.ResidueField (curvePlaceCompletionIntegers v)))
    IsLocalRing.residue_surjective
    (curvePlaceSmallCompletionResiduePlaces_lt k F _ v hv) p

/-- Uniform exact integral lifts at all finite places of a number field
outside one finite set, retaining the original coefficient base. -/
def numberFieldComponentAlmostAllIntegralPointLifts
    (hLW : UniformLangWeilStatement.{u})
    (K : Type u) [Field K] [NumberField K]
    (C : Type u) [CommRing C] (B Y : Over (Spec (CommRingCat.of C)))
    (f : Y ⟶ B)
    (hBft : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from B.left))
    (hBqc : CompactSpace B.left) (hsmooth : Smooth f.left)
    (hsep : _root_.AlgebraicGeometry.IsSeparated f.left) (hqc : QuasiCompact f.left)
    (hconn : GeometricallyConnected f.left) :
    Σ S : Finset (FinitePlace K),
      (v : FinitePlace K) → v ∉ S →
        [Algebra C (v.adicCompletionIntegers K)] →
        (p : RingPoint C B (v.adicCompletionIntegers K)) →
        {a : RingPoint C Y (v.adicCompletionIntegers K) // a ≫ f = p} := by
  let lifts := uniformLangWeilComponentHenselianRingPointLifts hLW C B Y f
    hBft hBqc hsmooth hsep hqc hconn
  refine ⟨finitePlaceSmallCompletionResiduePlaces K (lifts.1.1 ^ 2),
    fun v hv _ p => ?_⟩
  let : HenselianLocalRing (v.adicCompletionIntegers K) :=
    adicCompletionIntegers_henselian (NumberField.RingOfIntegers K) K v
  exact lifts.2 (v.adicCompletionIntegers K)
    (IsLocalRing.ResidueField (v.adicCompletionIntegers K))
    (IsScalarTower.toAlgHom C (v.adicCompletionIntegers K)
      (IsLocalRing.ResidueField (v.adicCompletionIntegers K)))
    IsLocalRing.residue_surjective
    (finitePlaceSmallCompletionResiduePlaces_lt K _ v hv) p

open scoped Langlands.Global.FixedModelLocalProduct

section Curve

variable (hLW : UniformLangWeilStatement.{u})
  (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
  (S : Finset (AlgebraicCurve.Place k F))
  (B Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
  (f : Y ⟶ B)
  (hBft : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from B.left))
  (hBqc : CompactSpace B.left) (hsmooth : Smooth f.left)
  (hsep : _root_.AlgebraicGeometry.IsSeparated f.left) (hqc : QuasiCompact f.left)
  (hconn : GeometricallyConnected f.left)

/-- At each enlarged level, construct a finite set of exceptional factors
and exact lifts at all other original fixed-base factors. -/
def curvePlaceLevelComponentPointLifts (T : AdelicLevelIndexAbove S) :
    Σ E : Finset (CurvePlaceLevelFactorIndex k F T.val),
      (i : CurvePlaceLevelFactorIndex k F T.val) → i ∉ E →
        (p : RingPoint (curvePlaceSIntegers k F S) B (CurvePlaceLevelFactor k F T.val i)) →
        {a : RingPoint (curvePlaceSIntegers k F S) Y (CurvePlaceLevelFactor k F T.val i) //
          a ≫ f = p} := by
  classical
  let lifts := curvePlaceComponentAlmostAllIntegralPointLifts hLW k F (curvePlaceSIntegers k F S)
    B Y f hBft hBqc hsmooth hsep hqc hconn
  let small : Set {v : AlgebraicCurve.Place k F // v ∉ T.val} :=
    {v | v.1 ∈ lifts.1}
  have hsmall : small.Finite :=
    lifts.1.finite_toSet.preimage Subtype.val_injective.injOn
  let bad : Set (CurvePlaceLevelFactorIndex k F T.val) :=
    Set.range Sum.inl ∪ Sum.inr '' small
  have hbad : bad.Finite := (Set.finite_range Sum.inl).union (hsmall.image Sum.inr)
  refine ⟨hbad.toFinset, fun i hi p => ?_⟩
  cases i with
  | inl v =>
    exact False.elim (hi (hbad.mem_toFinset.mpr (Or.inl ⟨v, rfl⟩)))
  | inr v =>
    have hv : v.1 ∉ lifts.1 := by
      intro h
      exact hi (hbad.mem_toFinset.mpr (Or.inr ⟨v, h, rfl⟩))
    let : Algebra (curvePlaceSIntegers k F S) (curvePlaceCompletionIntegers v.1) :=
      inferInstanceAs (Algebra (curvePlaceSIntegers k F S)
        (CurvePlaceLevelFactor k F T.val (.inr v)))
    exact lifts.2 v.1 hv p

include hLW hBft hBqc hsmooth hsep hqc hconn in
/-- The actual cofinite-surjectivity hypothesis needed by the fixed-model
adelic openness reduction, at every enlarged level. -/
theorem curvePlaceLevel_component_eventually_surjective (T : AdelicLevelIndexAbove S) :
    ∀ᶠ i in Filter.cofinite, Function.Surjective
      (fun p : RingPoint (curvePlaceSIntegers k F S) Y (CurvePlaceLevelFactor k F T.val i) =>
        p ≫ f) := by
  let lifts := curvePlaceLevelComponentPointLifts hLW k F S B Y f hBft hBqc
    hsmooth hsep hqc hconn T
  filter_upwards [lifts.1.eventually_cofinite_notMem] with i hi
  intro p
  exact ⟨(lifts.2 i hi p).1, (lifts.2 i hi p).2⟩

end Curve

section NumberField

variable (hLW : UniformLangWeilStatement.{u})
  (K : Type u) [Field K] [NumberField K]
  (S : Finset (FinitePlace K))
  (B Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
  (f : Y ⟶ B)
  (hBft : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from B.left))
  (hBqc : CompactSpace B.left) (hsmooth : Smooth f.left)
  (hsep : _root_.AlgebraicGeometry.IsSeparated f.left) (hqc : QuasiCompact f.left)
  (hconn : GeometricallyConnected f.left)

/-- Retain every infinite factor and every supported finite field factor
as an explicit exceptional index; construct lifts at all remaining factors. -/
def numberFieldLevelComponentPointLifts (T : AdelicLevelIndexAbove S) :
    Σ E : Finset (NumberFieldLevelFactorIndex K T.val),
      (i : NumberFieldLevelFactorIndex K T.val) → i ∉ E →
        (p : RingPoint ((S : Set (FinitePlace K)).integer K) B
          (NumberFieldLevelFactor K T.val i)) →
        {a : RingPoint ((S : Set (FinitePlace K)).integer K) Y
          (NumberFieldLevelFactor K T.val i) // a ≫ f = p} := by
  classical
  let lifts := numberFieldComponentAlmostAllIntegralPointLifts hLW K
    ((S : Set (FinitePlace K)).integer K) B Y f hBft hBqc hsmooth hsep hqc hconn
  let small : Set {v : FinitePlace K // v ∉ T.val} := {v | v.1 ∈ lifts.1}
  have hsmall : small.Finite :=
    lifts.1.finite_toSet.preimage Subtype.val_injective.injOn
  let bad : Set (NumberFieldLevelFactorIndex K T.val) :=
    (Set.range Sum.inl ∪ Set.range
      (fun v : {v : FinitePlace K // v ∈ T.val} => Sum.inr (Sum.inl v))) ∪
        (fun v => Sum.inr (Sum.inr v)) '' small
  have hbad : bad.Finite :=
    ((Set.finite_range Sum.inl).union (Set.finite_range _)).union (hsmall.image _)
  refine ⟨hbad.toFinset, fun i hi p => ?_⟩
  cases i with
  | inl v =>
    exact False.elim (hi (hbad.mem_toFinset.mpr (Or.inl (Or.inl ⟨v, rfl⟩))))
  | inr j =>
    cases j with
    | inl v =>
      exact False.elim (hi (hbad.mem_toFinset.mpr (Or.inl (Or.inr ⟨v, rfl⟩))))
    | inr v =>
      have hv : v.1 ∉ lifts.1 := by
        intro h
        exact hi (hbad.mem_toFinset.mpr (Or.inr ⟨v, h, rfl⟩))
      let : Algebra ((S : Set (FinitePlace K)).integer K) (v.1.adicCompletionIntegers K) :=
        inferInstanceAs (Algebra ((S : Set (FinitePlace K)).integer K)
          (NumberFieldLevelFactor K T.val (.inr (.inr v))))
      exact lifts.2 v.1 hv p

include hLW hBft hBqc hsmooth hsep hqc hconn in
/-- Every full number-field level satisfies the actual cofinite-surjectivity
hypothesis, with its original fixed coefficient actions. -/
theorem numberFieldLevel_component_eventually_surjective (T : AdelicLevelIndexAbove S) :
    ∀ᶠ i in Filter.cofinite, Function.Surjective
      (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) Y
        (NumberFieldLevelFactor K T.val i) => p ≫ f) := by
  let lifts := numberFieldLevelComponentPointLifts hLW K S B Y f hBft hBqc
    hsmooth hsep hqc hconn T
  filter_upwards [lifts.1.eventually_cofinite_notMem] with i hi
  intro p
  exact ⟨(lifts.2 i hi p).1, (lifts.2 i hi p).2⟩

end NumberField

/-- The actual cofinite local surjectivity input in both characteristics. -/
theorem adelicLevelComponentSurjectivity : AdelicLevelComponentSurjectivityStatement.{u} := by
  constructor
  · intro hLW k F _ _ _ _ _ _ _ S B Y f hBft hBqc hsmooth hsep hqc hconn T
    exact curvePlaceLevel_component_eventually_surjective hLW k F S B Y f
      hBft hBqc hsmooth hsep hqc hconn T
  · intro hLW K _ _ S B Y f hBft hBqc hsmooth hsep hqc hconn T
    exact numberFieldLevel_component_eventually_surjective hLW K S B Y f
      hBft hBqc hsmooth hsep hqc hconn T

end Langlands.Global
