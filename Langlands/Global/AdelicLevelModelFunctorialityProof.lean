import Langlands.Global.AdelicLevelModelFunctorialityStatement
import Langlands.Global.AdelicLocalFactorUnitsProof
import Langlands.AlgebraicGeometry.PointTopology.SchemeOpenPointProofs

/-! # Continuity of actual adelic-level model postcomposition -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Actual model postcomposition is continuous at every fixed arithmetic level. -/
theorem adelicLevelModelFunctoriality : AdelicLevelModelFunctorialityStatement.{u} := by
  constructor
  · intro k F _ _ _ S X Y f
    let (i : CurvePlaceLevelFactorIndex k F S) : IsOpenUnits (CurvePlaceLevelFactor k F S i) :=
      adelicLocalFactorUnits.1 k F S i
    let : TopologicalSpace (RingPoint (curvePlaceSIntegers k F S) X
        (curvePlaceAdeleLevel k F S)) := curvePlaceLevelModelPointTopology k F S X
    let : TopologicalSpace (RingPoint (curvePlaceSIntegers k F S) Y
        (curvePlaceAdeleLevel k F S)) := curvePlaceLevelModelPointTopology k F S Y
    let (i : CurvePlaceLevelFactorIndex k F S) : TopologicalSpace
        (RingPoint (CurvePlaceLevelFactor k F S i)
          (ringBaseChange (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S i) X)
          (CurvePlaceLevelFactor k F S i)) :=
      schemePointTopology _ _ _
    let (i : CurvePlaceLevelFactorIndex k F S) : TopologicalSpace
        (RingPoint (CurvePlaceLevelFactor k F S i)
          (ringBaseChange (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S i) Y)
          (CurvePlaceLevelFactor k F S i)) :=
      schemePointTopology _ _ _
    apply (curvePlaceLevelModelPointMap_isInducing k F S Y).continuous_iff.mpr
    apply continuous_pi
    intro i
    have hlocal := schemePointContinuity_proof (CurvePlaceLevelFactor k F S i)
      (CurvePlaceLevelFactor k F S i)
      (ringBaseChange (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S i) X)
      (ringBaseChange (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S i) Y)
      ((Over.pullback (Spec.algebraMap (curvePlaceSIntegers k F S)
        (CurvePlaceLevelFactor k F S i))).map f)
    have hcoord := (continuous_apply i).comp
      (curvePlaceLevelModelPointMap_isInducing k F S X).continuous
    refine (hlocal.comp hcoord).congr ?_
    intro p
    symm
    change ringPointBaseChangeEquiv (curvePlaceSIntegers k F S)
      (CurvePlaceLevelFactor k F S i) (CurvePlaceLevelFactor k F S i) Y
      (RingPoint.changeRing (curvePlaceLevelFactorAlgHom k F S i) (p ≫ f)) =
        ringPointBaseChangeEquiv (curvePlaceSIntegers k F S)
          (CurvePlaceLevelFactor k F S i) (CurvePlaceLevelFactor k F S i) X
          (RingPoint.changeRing (curvePlaceLevelFactorAlgHom k F S i) p) ≫ _
    rw [show RingPoint.changeRing (curvePlaceLevelFactorAlgHom k F S i) (p ≫ f) =
      RingPoint.changeRing (curvePlaceLevelFactorAlgHom k F S i) p ≫ f from
        (Category.assoc _ _ _).symm]
    exact ringPointBaseChangeEquiv_natural (curvePlaceSIntegers k F S)
      (CurvePlaceLevelFactor k F S i) (CurvePlaceLevelFactor k F S i) f _
  · intro K _ _ S X Y f
    let (i : NumberFieldLevelFactorIndex K S) : IsOpenUnits (NumberFieldLevelFactor K S i) :=
      adelicLocalFactorUnits.2 K S i
    let : TopologicalSpace (RingPoint ((S : Set (FinitePlace K)).integer K) X
        (numberFieldAdeleLevel K S)) := numberFieldLevelModelPointTopology K S X
    let : TopologicalSpace (RingPoint ((S : Set (FinitePlace K)).integer K) Y
        (numberFieldAdeleLevel K S)) := numberFieldLevelModelPointTopology K S Y
    let (i : NumberFieldLevelFactorIndex K S) : TopologicalSpace
        (RingPoint (NumberFieldLevelFactor K S i)
          (ringBaseChange ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K S i) X)
          (NumberFieldLevelFactor K S i)) :=
      schemePointTopology _ _ _
    let (i : NumberFieldLevelFactorIndex K S) : TopologicalSpace
        (RingPoint (NumberFieldLevelFactor K S i)
          (ringBaseChange ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K S i) Y)
          (NumberFieldLevelFactor K S i)) :=
      schemePointTopology _ _ _
    apply (numberFieldLevelModelPointMap_isInducing K S Y).continuous_iff.mpr
    apply continuous_pi
    intro i
    have hlocal := schemePointContinuity_proof (NumberFieldLevelFactor K S i)
      (NumberFieldLevelFactor K S i)
      (ringBaseChange ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K S i) X)
      (ringBaseChange ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K S i) Y)
      ((Over.pullback (Spec.algebraMap ((S : Set (FinitePlace K)).integer K)
        (NumberFieldLevelFactor K S i))).map f)
    have hcoord := (continuous_apply i).comp
      (numberFieldLevelModelPointMap_isInducing K S X).continuous
    refine (hlocal.comp hcoord).congr ?_
    intro p
    symm
    change ringPointBaseChangeEquiv ((S : Set (FinitePlace K)).integer K)
      (NumberFieldLevelFactor K S i) (NumberFieldLevelFactor K S i) Y
      (RingPoint.changeRing (numberFieldLevelFactorAlgHom K S i) (p ≫ f)) =
        ringPointBaseChangeEquiv ((S : Set (FinitePlace K)).integer K)
          (NumberFieldLevelFactor K S i) (NumberFieldLevelFactor K S i) X
          (RingPoint.changeRing (numberFieldLevelFactorAlgHom K S i) p) ≫ _
    rw [show RingPoint.changeRing (numberFieldLevelFactorAlgHom K S i) (p ≫ f) =
      RingPoint.changeRing (numberFieldLevelFactorAlgHom K S i) p ≫ f from
        (Category.assoc _ _ _).symm]
    exact ringPointBaseChangeEquiv_natural ((S : Set (FinitePlace K)).integer K)
      (NumberFieldLevelFactor K S i) (NumberFieldLevelFactor K S i) f _

end Langlands.Global
