import Langlands.Global.AdelicAlmostAllIntegralLifts
import Langlands.Global.AdelicFixedModelLocalProductTopology

/-! # Almost-all lifts in the original fixed-base adelic level factors -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped Langlands.Global.FixedModelLocalProduct

section Curve

variable (hLW : UniformLangWeilStatement.{u})
  (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
  (S : Finset (AlgebraicCurve.Place k F))
  (B Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
  (f : Y ⟶ B) (d : ℕ)
  (hBft : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from B.left))
  (hBqc : CompactSpace B.left) (hsmooth : Smooth f.left)
  (hsep : _root_.AlgebraicGeometry.IsSeparated f.left) (hsurj : Surjective f.left)
  (hft : LocallyOfFiniteType f.left) (hqc : QuasiCompact f.left)
  (hconn : GeometricallyConnected f.left)
  (hdim : ∀ b : B.left, SchemeFiberGeometry.HasPureDimension (f.left.fiber b) d)

/-- At each enlarged level, construct a finite set of exceptional factors
and exact lifts at all other original fixed-base factors. -/
def curvePlaceLevelAlmostAllPointLifts (T : AdelicLevelIndexAbove S) :
    Σ E : Finset (CurvePlaceLevelFactorIndex k F T.val),
      (i : CurvePlaceLevelFactorIndex k F T.val) → i ∉ E →
        (p : RingPoint (curvePlaceSIntegers k F S) B (CurvePlaceLevelFactor k F T.val i)) →
        {a : RingPoint (curvePlaceSIntegers k F S) Y (CurvePlaceLevelFactor k F T.val i) //
          a ≫ f = p} := by
  classical
  let lifts := curvePlaceAlmostAllIntegralPointLifts hLW k F (curvePlaceSIntegers k F S)
    B Y f d hBft hBqc hsmooth hsep hsurj hft hqc hconn hdim
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

include hLW hBft hBqc hsmooth hsep hsurj hft hqc hconn hdim in
/-- The actual cofinite-surjectivity hypothesis needed by the fixed-model
adelic openness reduction, at every enlarged level. -/
theorem curvePlaceLevel_eventually_surjective (T : AdelicLevelIndexAbove S) :
    ∀ᶠ i in Filter.cofinite, Function.Surjective
      (fun p : RingPoint (curvePlaceSIntegers k F S) Y (CurvePlaceLevelFactor k F T.val i) =>
        p ≫ f) := by
  let lifts := curvePlaceLevelAlmostAllPointLifts hLW k F S B Y f d hBft hBqc
    hsmooth hsep hsurj hft hqc hconn hdim T
  filter_upwards [lifts.1.eventually_cofinite_notMem] with i hi
  intro p
  exact ⟨(lifts.2 i hi p).1, (lifts.2 i hi p).2⟩

end Curve

section NumberField

variable (hLW : UniformLangWeilStatement.{u})
  (K : Type u) [Field K] [NumberField K]
  (S : Finset (FinitePlace K))
  (B Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
  (f : Y ⟶ B) (d : ℕ)
  (hBft : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from B.left))
  (hBqc : CompactSpace B.left) (hsmooth : Smooth f.left)
  (hsep : _root_.AlgebraicGeometry.IsSeparated f.left) (hsurj : Surjective f.left)
  (hft : LocallyOfFiniteType f.left) (hqc : QuasiCompact f.left)
  (hconn : GeometricallyConnected f.left)
  (hdim : ∀ b : B.left, SchemeFiberGeometry.HasPureDimension (f.left.fiber b) d)

/-- Retain every infinite factor and every supported finite field factor
as an explicit exceptional index; construct lifts at all remaining factors. -/
def numberFieldLevelAlmostAllPointLifts (T : AdelicLevelIndexAbove S) :
    Σ E : Finset (NumberFieldLevelFactorIndex K T.val),
      (i : NumberFieldLevelFactorIndex K T.val) → i ∉ E →
        (p : RingPoint ((S : Set (FinitePlace K)).integer K) B
          (NumberFieldLevelFactor K T.val i)) →
        {a : RingPoint ((S : Set (FinitePlace K)).integer K) Y
          (NumberFieldLevelFactor K T.val i) // a ≫ f = p} := by
  classical
  let lifts := numberFieldAlmostAllIntegralPointLifts hLW K
    ((S : Set (FinitePlace K)).integer K) B Y f d hBft hBqc hsmooth hsep hsurj
    hft hqc hconn hdim
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

include hLW hBft hBqc hsmooth hsep hsurj hft hqc hconn hdim in
/-- Every full number-field level satisfies the actual cofinite-surjectivity
hypothesis, with its original fixed coefficient actions. -/
theorem numberFieldLevel_eventually_surjective (T : AdelicLevelIndexAbove S) :
    ∀ᶠ i in Filter.cofinite, Function.Surjective
      (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) Y
        (NumberFieldLevelFactor K T.val i) => p ≫ f) := by
  let lifts := numberFieldLevelAlmostAllPointLifts hLW K S B Y f d hBft hBqc
    hsmooth hsep hsurj hft hqc hconn hdim T
  filter_upwards [lifts.1.eventually_cofinite_notMem] with i hi
  intro p
  exact ⟨(lifts.2 i hi p).1, (lifts.2 i hi p).2⟩

end NumberField

end Langlands.Global
