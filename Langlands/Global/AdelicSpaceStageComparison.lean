import Langlands.Global.AdelicSpacePointTopology
import Langlands.Topology.FinalStageComparison

/-!
# Comparing spread topologies through arithmetic stages

An equivalence between field-valued adelic point sets is a homeomorphism
whenever its transport to model points and its inverse lift continuously
between arithmetic stages. No independence or existence of models is used.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.Topology

namespace Langlands.Global

section CurveSpread

variable (k F : Type u) [Field k] [PerfectField k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
variable (S : Finset (AlgebraicCurve.Place k F))
variable (X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
variable (Y : AlgebraicSpace (Spec (CommRingCat.of F)))
variable (e : curvePlaceSpaceGenericFiber k F S X ≅ Y)

/-- The equivalence that defines a curve-place spread topology is a homeomorphism. -/
def curvePlaceSpaceSpreadHomeomorph :
    @Homeomorph (CurvePlaceSpaceAdelePoints k F S X) (CurvePlaceSpaceFieldAdelePoints k F Y)
      (curvePlaceSpaceAdelePointTopology k F S X) (curvePlaceSpaceSpreadTopology k F S X Y e) := by
  letI := curvePlaceSpaceAdelePointTopology k F S X
  letI := curvePlaceSpaceSpreadTopology k F S X Y e
  exact ((curvePlaceSpaceSpreadEquiv k F S X Y e).symm.toHomeomorphOfIsInducing ⟨rfl⟩).symm

end CurveSpread

section CurveComparison

variable (k F F' : Type u) [Field k] [PerfectField k] [Field F] [Field F']
variable [Algebra k F] [Algebra k F']
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
variable [Algebra (RatFunc k) F'] [IsScalarTower k (RatFunc k) F'] [FunctionField k F']
variable (S : Finset (AlgebraicCurve.Place k F)) (S' : Finset (AlgebraicCurve.Place k F'))
variable (X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
variable (X' : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F' S'))))
variable (Y : AlgebraicSpace (Spec (CommRingCat.of F)))
variable (Y' : AlgebraicSpace (Spec (CommRingCat.of F')))
variable (e : curvePlaceSpaceGenericFiber k F S X ≅ Y)
variable (e' : curvePlaceSpaceGenericFiber k F' S' X' ≅ Y')
variable (E : CurvePlaceSpaceFieldAdelePoints k F Y ≃ CurvePlaceSpaceFieldAdelePoints k F' Y')

/-- Transport a comparison of field points to the points of the specified models. -/
def curvePlaceSpaceSpreadComparisonEquiv :
    CurvePlaceSpaceAdelePoints k F S X ≃ CurvePlaceSpaceAdelePoints k F' S' X' :=
  ((curvePlaceSpaceSpreadEquiv k F S X Y e).trans E).trans
    (curvePlaceSpaceSpreadEquiv k F' S' X' Y' e').symm

local instance lowerCurveStageTopology (T : AdelicLevelIndexAbove S) :
    TopologicalSpace
      (RingPoints (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T)) :=
  curvePlaceSpaceStageTopology k F S X T

local instance upperCurveStageTopology (T : AdelicLevelIndexAbove S') :
    TopologicalSpace
      (RingPoints (curvePlaceSIntegers k F' S') X' (curvePlaceAdeleLevelOver k F' S' T)) :=
  curvePlaceSpaceStageTopology k F' S' X' T

variable
  (hf : HasContinuousStageLifts (curvePlaceSpaceStageMap k F S X)
    (curvePlaceSpaceStageMap k F' S' X')
    (curvePlaceSpaceSpreadComparisonEquiv k F F' S S' X X' Y Y' e e' E))
  (hb : HasContinuousStageLifts (curvePlaceSpaceStageMap k F' S' X')
    (curvePlaceSpaceStageMap k F S X)
    (curvePlaceSpaceSpreadComparisonEquiv k F F' S S' X X' Y Y' e e' E).symm)

/-- Continuous stage lifts in both directions identify the specified spread topologies. -/
def curvePlaceSpaceSpreadHomeomorphOfStageLifts :
    @Homeomorph (CurvePlaceSpaceFieldAdelePoints k F Y) (CurvePlaceSpaceFieldAdelePoints k F' Y')
      (curvePlaceSpaceSpreadTopology k F S X Y e)
      (curvePlaceSpaceSpreadTopology k F' S' X' Y' e') := by
  letI := curvePlaceSpaceAdelePointTopology k F S X
  letI := curvePlaceSpaceAdelePointTopology k F' S' X'
  letI := curvePlaceSpaceSpreadTopology k F S X Y e
  letI := curvePlaceSpaceSpreadTopology k F' S' X' Y' e'
  exact (curvePlaceSpaceSpreadHomeomorph k F S X Y e).symm.trans
    ((homeomorphOfStageLifts _ _
      (curvePlaceSpaceSpreadComparisonEquiv k F F' S S' X X' Y Y' e e' E) hf hb).trans
        (curvePlaceSpaceSpreadHomeomorph k F' S' X' Y' e'))

/-- The assembled homeomorphism has exactly the initially specified map on field points. -/
@[simp]
theorem curvePlaceSpaceSpreadHomeomorphOfStageLifts_apply
    (x : CurvePlaceSpaceFieldAdelePoints k F Y) :
    curvePlaceSpaceSpreadHomeomorphOfStageLifts k F F' S S' X X' Y Y' e e' E hf hb x = E x := by
  change (curvePlaceSpaceSpreadEquiv k F' S' X' Y' e')
    ((curvePlaceSpaceSpreadEquiv k F' S' X' Y' e').symm
      (E ((curvePlaceSpaceSpreadEquiv k F S X Y e)
        ((curvePlaceSpaceSpreadEquiv k F S X Y e).symm x)))) = E x
  simp only [Equiv.apply_symm_apply]

end CurveComparison

section NumberFieldSpread

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
variable (X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
variable (Y : AlgebraicSpace (Spec (CommRingCat.of K)))
variable (e : numberFieldSpaceGenericFiber K S X ≅ Y)

/-- The equivalence that defines a number-field spread topology is a homeomorphism. -/
def numberFieldSpaceSpreadHomeomorph :
    @Homeomorph (NumberFieldSpaceAdelePoints K S X) (NumberFieldSpaceFieldAdelePoints K Y)
      (numberFieldSpaceAdelePointTopology K S X) (numberFieldSpaceSpreadTopology K S X Y e) := by
  letI := numberFieldSpaceAdelePointTopology K S X
  letI := numberFieldSpaceSpreadTopology K S X Y e
  exact ((numberFieldSpaceSpreadEquiv K S X Y e).symm.toHomeomorphOfIsInducing ⟨rfl⟩).symm

end NumberFieldSpread

section NumberFieldComparison

variable (K K' : Type u) [Field K] [NumberField K] [Field K'] [NumberField K']
variable (S : Finset (FinitePlace K)) (S' : Finset (FinitePlace K'))
variable (X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
variable (X' : AlgebraicSpace (Spec (CommRingCat.of ((S' : Set (FinitePlace K')).integer K'))))
variable (Y : AlgebraicSpace (Spec (CommRingCat.of K)))
variable (Y' : AlgebraicSpace (Spec (CommRingCat.of K')))
variable (e : numberFieldSpaceGenericFiber K S X ≅ Y)
variable (e' : numberFieldSpaceGenericFiber K' S' X' ≅ Y')
variable (E : NumberFieldSpaceFieldAdelePoints K Y ≃ NumberFieldSpaceFieldAdelePoints K' Y')

/-- Transport a comparison of full number-field adelic points to the model points. -/
def numberFieldSpaceSpreadComparisonEquiv :
    NumberFieldSpaceAdelePoints K S X ≃ NumberFieldSpaceAdelePoints K' S' X' :=
  ((numberFieldSpaceSpreadEquiv K S X Y e).trans E).trans
    (numberFieldSpaceSpreadEquiv K' S' X' Y' e').symm

local instance lowerNumberFieldStageTopology (T : AdelicLevelIndexAbove S) :
    TopologicalSpace (RingPoints ((S : Set (FinitePlace K)).integer K) X
      (numberFieldAdeleLevelOver K S T)) :=
  numberFieldSpaceStageTopology K S X T

local instance upperNumberFieldStageTopology (T : AdelicLevelIndexAbove S') :
    TopologicalSpace (RingPoints ((S' : Set (FinitePlace K')).integer K') X'
      (numberFieldAdeleLevelOver K' S' T)) :=
  numberFieldSpaceStageTopology K' S' X' T

variable
  (hf : HasContinuousStageLifts (numberFieldSpaceStageMap K S X)
    (numberFieldSpaceStageMap K' S' X')
    (numberFieldSpaceSpreadComparisonEquiv K K' S S' X X' Y Y' e e' E))
  (hb : HasContinuousStageLifts (numberFieldSpaceStageMap K' S' X')
    (numberFieldSpaceStageMap K S X)
    (numberFieldSpaceSpreadComparisonEquiv K K' S S' X X' Y Y' e e' E).symm)

/-- Continuous stage lifts in both directions identify full adelic spread topologies. -/
def numberFieldSpaceSpreadHomeomorphOfStageLifts :
    @Homeomorph (NumberFieldSpaceFieldAdelePoints K Y) (NumberFieldSpaceFieldAdelePoints K' Y')
      (numberFieldSpaceSpreadTopology K S X Y e)
      (numberFieldSpaceSpreadTopology K' S' X' Y' e') := by
  letI := numberFieldSpaceAdelePointTopology K S X
  letI := numberFieldSpaceAdelePointTopology K' S' X'
  letI := numberFieldSpaceSpreadTopology K S X Y e
  letI := numberFieldSpaceSpreadTopology K' S' X' Y' e'
  exact (numberFieldSpaceSpreadHomeomorph K S X Y e).symm.trans
    ((homeomorphOfStageLifts _ _
      (numberFieldSpaceSpreadComparisonEquiv K K' S S' X X' Y Y' e e' E) hf hb).trans
        (numberFieldSpaceSpreadHomeomorph K' S' X' Y' e'))

/-- The assembled homeomorphism has exactly the initially specified field-point map. -/
@[simp]
theorem numberFieldSpaceSpreadHomeomorphOfStageLifts_apply
    (x : NumberFieldSpaceFieldAdelePoints K Y) :
    numberFieldSpaceSpreadHomeomorphOfStageLifts K K' S S' X X' Y Y' e e' E hf hb x = E x := by
  change (numberFieldSpaceSpreadEquiv K' S' X' Y' e')
    ((numberFieldSpaceSpreadEquiv K' S' X' Y' e').symm
      (E ((numberFieldSpaceSpreadEquiv K S X Y e)
        ((numberFieldSpaceSpreadEquiv K S X Y e).symm x)))) = E x
  simp only [Equiv.apply_symm_apply]

end NumberFieldComparison

end Langlands.Global
