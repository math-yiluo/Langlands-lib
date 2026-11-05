import Langlands.Global.AdelicLevelModelSecondCountabilityStatement
import Langlands.Global.AdelicLocalFactorUnitsProof
import Langlands.Global.FunctionFieldAdelesSecondCountableProof
import Langlands.AlgebraicGeometry.PointTopology.PointSecondCountabilityProof

/-! # Second countability of actual arithmetic-level model points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (C R : Type u) [CommRing C] [CommRing R] [Algebra C R]
variable (X : Over (Spec (CommRingCat.of C)))
variable [TopologicalSpace R] [IsTopologicalRing R] [SecondCountableTopology R]
variable [IsLocalRing R] [IsOpenUnits R]

private theorem localModelPoint_secondCountableTopology
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    @SecondCountableTopology (RingPoint R (ringBaseChange C R X) R)
      (schemePointTopology R (ringBaseChange C R X) R) := by
  let : LocallyOfFiniteType (ringBaseChange C R X).hom := by
    change LocallyOfFiniteType (pullback.snd X.hom (Spec.algebraMap C R))
    infer_instance
  let : QuasiCompact (ringBaseChange C R X).hom := by
    change QuasiCompact (pullback.snd X.hom (Spec.algebraMap C R))
    infer_instance
  exact schemePointSecondCountability R R (ringBaseChange C R X)

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
variable (S : Finset (AlgebraicCurve.Place k F))
variable (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
variable [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]

/-- Countably many second-countable local-model factors give the actual level result. -/
theorem curvePlaceLevelModelPoint_secondCountableTopology :
    @SecondCountableTopology
      (RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S))
      (curvePlaceLevelModelPointTopology k F S X) := by
  let := curvePlaceLevelModelPointTopology k F S X
  let : Countable (AlgebraicCurve.Place k F) := curvePlace_countable k F
  let P (i : CurvePlaceLevelFactorIndex k F S) :=
    RingPoint (CurvePlaceLevelFactor k F S i)
      (ringBaseChange (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S i) X)
      (CurvePlaceLevelFactor k F S i)
  let : ∀ i, TopologicalSpace (P i) := fun i =>
    schemePointTopology (CurvePlaceLevelFactor k F S i)
      (ringBaseChange (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S i) X)
      (CurvePlaceLevelFactor k F S i)
  let : ∀ i, IsOpenUnits (CurvePlaceLevelFactor k F S i) :=
    adelicLocalFactorUnits.1 k F S
  let : ∀ i, SecondCountableTopology (CurvePlaceLevelFactor k F S i) := by
    intro i
    cases i with
    | inl v => exact curvePlaceCompletion_secondCountableTopology k F v.1
    | inr v =>
      let := curvePlaceCompletion_secondCountableTopology k F v.1
      exact TopologicalSpace.Subtype.secondCountableTopology
        (curvePlaceCompletionIntegers v.1 : Set (curvePlaceCompletion v.1))
  let : ∀ i, SecondCountableTopology (P i) := fun i =>
    localModelPoint_secondCountableTopology (curvePlaceSIntegers k F S)
      (CurvePlaceLevelFactor k F S i) X
  exact (curvePlaceLevelModelPointMap_isInducing k F S X).secondCountableTopology

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
variable (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
variable [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]

/-- The countable product includes every archimedean completion. -/
theorem numberFieldLevelModelPoint_secondCountableTopology :
    @SecondCountableTopology
      (RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S))
      (numberFieldLevelModelPointTopology K S X) := by
  let := numberFieldLevelModelPointTopology K S X
  let : Countable (FinitePlace K) := finitePlace_countable K
  let P (i : NumberFieldLevelFactorIndex K S) :=
    RingPoint (NumberFieldLevelFactor K S i)
      (ringBaseChange ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K S i) X)
      (NumberFieldLevelFactor K S i)
  let : ∀ i, TopologicalSpace (P i) := fun i =>
    schemePointTopology (NumberFieldLevelFactor K S i)
      (ringBaseChange ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K S i) X)
      (NumberFieldLevelFactor K S i)
  let : ∀ i, IsOpenUnits (NumberFieldLevelFactor K S i) :=
    adelicLocalFactorUnits.2 K S
  let : ∀ i, SecondCountableTopology (NumberFieldLevelFactor K S i) := by
    intro i
    cases i with
    | inl v => exact infiniteCompletion_secondCountableTopology K v
    | inr j =>
      cases j with
      | inl v => exact finiteCompletion_secondCountableTopology K v.1
      | inr v =>
        let := finiteCompletion_secondCountableTopology K v.1
        exact TopologicalSpace.Subtype.secondCountableTopology
          (v.1.adicCompletionIntegers K : Set (FiniteCompletion K v.1))
  let : ∀ i, SecondCountableTopology (P i) := fun i =>
    localModelPoint_secondCountableTopology ((S : Set (FinitePlace K)).integer K)
      (NumberFieldLevelFactor K S i) X
  exact (numberFieldLevelModelPointMap_isInducing K S X).secondCountableTopology

end NumberField

/-- Second countability of the actual arithmetic-level point spaces in both characteristics. -/
theorem adelicLevelModelSecondCountability :
    AdelicLevelModelSecondCountabilityStatement.{u} := by
  constructor
  · intro k F _ _ _ _ _ _ _ S X _ _
    exact curvePlaceLevelModelPoint_secondCountableTopology k F S X
  · intro K _ _ S X _ _
    exact numberFieldLevelModelPoint_secondCountableTopology K S X

end Langlands.Global
