import Langlands.Automorphic.GroupSchemeParabolicMeasure
import Langlands.Global.LeftCosetSemidirectFiniteVolume

/-! # Actual mass-one radical quotient measures with proved Weil compatibility -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicSubgroupPoints

open Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] (U : SubgroupFunctor G)
  [hclosed : IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G))]
  [CompactSpace (RationalQuotient F G U)]

local instance compactWeilSubgroupLocallyCompactSpace : LocallyCompactSpace (adelicPoints F G U) :=
  hclosed.locallyCompactSpace

local instance compactWeilSubgroupPolishSpace : PolishSpace (adelicPoints F G U) :=
  hclosed.polishSpace

local instance compactWeilQuotientBorelSpace : BorelSpace (RationalQuotient F G U) :=
  rationalQuotientBorelSpace F G U

/-- Compactness of the actual rational quotient proves right invariance of actual subgroup Haar. -/
theorem haar_isMulRightInvariant_of_compactRationalQuotient :
    (Measure.haar : Measure (adelicPoints F G U)).IsMulRightInvariant := by
  let : IsFiniteMeasure
      (LeftCosetSpace.haarQuotientMeasure (rationalSubgroup F G U)
        (isDiscrete_rationalSubgroup F G U)) :=
    rationalQuotientHaarMeasure_isFiniteMeasure F G U
  exact LeftCosetSpace.isMulRightInvariant_haar_of_isFiniteMeasure
    (rationalSubgroup F G U) (isDiscrete_rationalSubgroup F G U)

/-- The unchanged intrinsic probability measure bundled with its derived exact Weil formula. -/
def compactCompatibleNormalizedRationalQuotientMeasure :
    {ν : Measure (RationalQuotient F G U) //
      IsProbabilityMeasure ν ∧
      Langlands.QuotientIntegration.IsCompatible (rationalSubgroup F G U)
        (normalizedHaarMeasure F G U) Measure.count ν} := by
  let := haar_isMulRightInvariant_of_compactRationalQuotient F G U
  exact ⟨normalizedRationalQuotientHaarMeasure F G U,
    normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G U,
    normalizedRationalQuotientHaarMeasure_isCompatible F G U⟩

@[simp]
theorem compactCompatibleNormalizedRationalQuotientMeasure_val :
    (compactCompatibleNormalizedRationalQuotientMeasure F G U).val =
      normalizedRationalQuotientHaarMeasure F G U := rfl

/-- Positive translation preserves the actual normalized probability with no supplied right-Haar gate. -/
theorem measurePreserving_rightTranslate_of_compactRationalQuotient
    (n : adelicPoints F G U) :
    MeasurePreserving (LeftCosetSpace.rightTranslate (rationalSubgroup F G U) n)
      (normalizedRationalQuotientHaarMeasure F G U)
      (normalizedRationalQuotientHaarMeasure F G U) := by
  let := haar_isMulRightInvariant_of_compactRationalQuotient F G U
  exact measurePreserving_rightTranslate_normalizedRationalQuotientHaarMeasure F G U n

end Langlands.Global.AdelicSubgroupPoints

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]
  (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)

/-- The actual complete proper-parabolic probability family now includes its proved Weil laws. -/
def properParabolicCompatibleProbabilityMeasure (P : ProperRationalParabolic G) :
    {ν : Measure (AdelicSubgroupPoints.RationalQuotient F G
      (properRationalParabolicRadicals hPD hG P)) //
      IsProbabilityMeasure ν ∧
      Langlands.QuotientIntegration.IsCompatible
        (AdelicSubgroupPoints.rationalSubgroup F G (properRationalParabolicRadicals hPD hG P))
        (properParabolicHaarMeasure F G hPD hG P) Measure.count ν} :=
  AdelicSubgroupPoints.compactCompatibleNormalizedRationalQuotientMeasure F G _

@[simp]
theorem properParabolicCompatibleProbabilityMeasure_val (P : ProperRationalParabolic G) :
    (properParabolicCompatibleProbabilityMeasure F G hPD hG P).val =
      properParabolicQuotientMeasure F G hPD hG P := rfl

/-- Exact compatibility of the existing mass-one measures has no subgroup right-Haar premise. -/
theorem properParabolicQuotientMeasure_isCompatible_of_compact
    (P : ProperRationalParabolic G) :
    Langlands.QuotientIntegration.IsCompatible
      (AdelicSubgroupPoints.rationalSubgroup F G (properRationalParabolicRadicals hPD hG P))
      (properParabolicHaarMeasure F G hPD hG P) Measure.count
      (properParabolicQuotientMeasure F G hPD hG P) :=
  (properParabolicCompatibleProbabilityMeasure F G hPD hG P).property.2

/-- Actual subgroup-left invariance of every normalized parabolic constant term is now derived. -/
theorem normalizedParabolicConstantTerm_subgroup_mul_of_compact
    (P : ProperRationalParabolic G) (f : ContinuousRationalFunctions F G)
    (n : AdelicSubgroupPoints.adelicPoints F G (properRationalParabolicRadicals hPD hG P))
    (g : AdelicGroupPoints F G) :
    constantTerm F G (properRationalParabolicRadicals hPD hG P)
        (properParabolicQuotientMeasure F G hPD hG P) f ((n : AdelicGroupPoints F G) * g) =
      constantTerm F G (properRationalParabolicRadicals hPD hG P)
        (properParabolicQuotientMeasure F G hPD hG P) f g := by
  let := AdelicSubgroupPoints.haar_isMulRightInvariant_of_compactRationalQuotient F G
    (properRationalParabolicRadicals hPD hG P)
  exact normalizedParabolicConstantTerm_subgroup_mul F G hPD hG P f n g

end Langlands.Automorphic.GroupSchemeFunctions
