import Langlands.Representation.Plancherel.DiscreteSeriesOrbitTopology
import Langlands.Representation.Plancherel.RationalTwistStabilizer
import Langlands.Representation.Plancherel.RationalUnramifiedCharacterCoordinates

/-! # Topology of actual rational-point discrete-series orbits -/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance instRationalDiscreteSeriesOrbitTopology1 : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X
local instance instRationalDiscreteSeriesOrbitTopology2 : NonarchimedeanGroup (GroupScheme.rationalPoints G) :=
  rationalPoints_nonarchimedeanGroup G

variable {T : CommGroupScheme (Spec (CommRingCat.of F))}
variable (s : T.toGrp ⟶ G) (hs : GroupScheme.IsCentral s)
variable [MeasurableSpace (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range)]
variable (mu : MeasureTheory.Measure
  (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range))

/-- Actual unitary twist orbits are compact in their quotient topology.
No actual-image finite-index premise is required. -/
theorem compactSpace_rationalDiscreteSeriesOrbit :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [MeasureTheory.Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
      CompactSpace (discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega) := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega
  let := compactSpace_rationalUnitaryUnramifiedCharacters G
  exact compactSpace_discreteSeriesOrbit _ _ _ _ omega

/-- The actual finite-index premise gives a finite closed stabilizer and hence
a Hausdorff orbit. -/
theorem t2Space_rationalDiscreteSeriesOrbit [IsAffine T.X.left]
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [MeasureTheory.Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
      T2Space (discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega) := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega
  let := finite_rationalDiscreteSeriesStabilizer s hs mu hindex omega
  exact t2Space_discreteSeriesOrbit _ _ _ _ omega

/-- The actual orbit map in the previously constructed finite circle
coordinates; no new character coordinates are chosen. -/
def rationalDiscreteSeriesOrbitCoordinateMap (hG : GroupScheme.IsConnectedReductive G) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [MeasureTheory.Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
      (Fin (rationalImageRank G) → Circle) →
        discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
          (fun psi => (rationalNormCharacters G psi).toMul) omega := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega
  exact discreteSeriesOrbitMap _ _ _ _ omega ∘
    (rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG).symm

@[simp]
theorem rationalDiscreteSeriesOrbitCoordinateMap_val
    (hG : GroupScheme.IsConnectedReductive G) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [MeasureTheory.Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (c : Fin (rationalImageRank G) → Circle),
      (rationalDiscreteSeriesOrbitCoordinateMap s hs mu hG omega c).val =
        (rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG).symm c • omega := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega c
  rfl

/-- Finite circle coordinates parameterize the actual orbit by an open
quotient map, with its existing quotient topology. -/
theorem isOpenQuotientMap_rationalDiscreteSeriesOrbitCoordinateMap
    (hG : GroupScheme.IsConnectedReductive G) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [MeasureTheory.Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
      IsOpenQuotientMap (rationalDiscreteSeriesOrbitCoordinateMap s hs mu hG omega) := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega
  exact (isOpenQuotientMap_discreteSeriesOrbitMap _ _ _ _ omega).comp
    (rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG).symm.toHomeomorph.isOpenQuotientMap

end Langlands.Plancherel
