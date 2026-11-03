import Langlands.Representation.Plancherel.RationalDiscreteSeriesOrbitTopology
import Langlands.Representation.Plancherel.DiscreteSeriesOrbitMeasure

/-! # Measures on actual rational-point discrete-series twist orbits -/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology MeasureTheory
open Langlands.AlgebraicGeometry.PointTopology
open scoped ENNReal NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance instRationalDiscreteSeriesOrbitMeasure1 : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X
local instance instRationalDiscreteSeriesOrbitMeasure2 : NonarchimedeanGroup (GroupScheme.rationalPoints G) :=
  rationalPoints_nonarchimedeanGroup G

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
variable (s : T.toGrp ⟶ G) (hs : GroupScheme.IsCentral s)
variable [MeasurableSpace (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range)]
variable (mu : Measure (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range))
variable (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)

/-- The actual-point orbit measure derives finite stabilizer from the explicit
actual-image finite-index premise and retains the supplied character scale. -/
def rationalDiscreteSeriesOrbitMeasure :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
      Measure (unitaryUnramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul)) →
        Measure (discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
          (fun psi => (rationalNormCharacters G psi).toMul) omega) := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega lambda
  let := finite_rationalDiscreteSeriesStabilizer s hs mu hindex omega
  exact discreteSeriesOrbitMeasure _ _ _ mu omega lambda

@[simp]
theorem rationalDiscreteSeriesOrbitMeasure_apply :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (lambda : Measure (unitaryUnramifiedCharacters
        (fun psi => (rationalNormCharacters G psi).toMul)))
      (E : Set (discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega)),
      MeasurableSet E → rationalDiscreteSeriesOrbitMeasure s hs mu hindex omega lambda E =
        (Nat.card (discreteSeriesStabilizer (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega) : ℝ≥0∞)⁻¹ *
          lambda (discreteSeriesOrbitMap (GroupScheme.rationalPoints.map s).range
            hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega ⁻¹' E) := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega lambda E hE
  let := finite_rationalDiscreteSeriesStabilizer s hs mu hindex omega
  exact discreteSeriesOrbitMeasure_apply _ _ _ mu omega lambda hE

@[simp]
theorem rationalDiscreteSeriesOrbitMeasure_univ :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (lambda : Measure (unitaryUnramifiedCharacters
        (fun psi => (rationalNormCharacters G psi).toMul))),
      rationalDiscreteSeriesOrbitMeasure s hs mu hindex omega lambda Set.univ =
        (Nat.card (discreteSeriesStabilizer (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega) : ℝ≥0∞)⁻¹ *
          lambda Set.univ := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega lambda
  let := finite_rationalDiscreteSeriesStabilizer s hs mu hindex omega
  exact discreteSeriesOrbitMeasure_univ _ _ _ mu omega lambda

/-- Rescaling the supplied actual character measure rescales the orbit measure. -/
theorem rationalDiscreteSeriesOrbitMeasure_smul :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (lambda : Measure (unitaryUnramifiedCharacters
        (fun psi => (rationalNormCharacters G psi).toMul))) (c : ℝ≥0∞),
      rationalDiscreteSeriesOrbitMeasure s hs mu hindex omega (c • lambda) =
        c • rationalDiscreteSeriesOrbitMeasure s hs mu hindex omega lambda := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega lambda c
  let := finite_rationalDiscreteSeriesStabilizer s hs mu hindex omega
  exact discreteSeriesOrbitMeasure_smul _ _ _ mu omega lambda c

/-- The actual rational-point twisting map locally preserves the supplied
invariant character measure. Its finite stabilizer is proved from hindex. -/
theorem isLocallyMeasurePreserving_rationalDiscreteSeriesOrbitMap :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (lambda : Measure (unitaryUnramifiedCharacters
        (fun psi => (rationalNormCharacters G psi).toMul))) [Measure.IsMulLeftInvariant lambda],
      IsLocallyMeasurePreserving
        (discreteSeriesOrbitMap (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega)
        lambda (rationalDiscreteSeriesOrbitMeasure s hs mu hindex omega lambda) := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega lambda _
  let := finite_rationalDiscreteSeriesStabilizer s hs mu hindex omega
  exact isLocallyMeasurePreserving_discreteSeriesOrbitMap _ _ _ mu omega lambda

/-- The identity on actual representation classes preserves the orbit measure
when the chosen base class is changed by a unitary unramified twist. -/
theorem map_rationalDiscreteSeriesOrbitMeasure_baseChange :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (chi : unitaryUnramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul))
      (lambda : Measure (unitaryUnramifiedCharacters
        (fun psi => (rationalNormCharacters G psi).toMul))) [Measure.IsMulLeftInvariant lambda],
      Measure.map (discreteSeriesOrbitBaseChange (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega chi)
        (rationalDiscreteSeriesOrbitMeasure s hs mu hindex (chi • omega) lambda) =
          rationalDiscreteSeriesOrbitMeasure s hs mu hindex omega lambda := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega chi lambda _
  let := finite_rationalDiscreteSeriesStabilizer s hs mu hindex omega
  let := finite_rationalDiscreteSeriesStabilizer s hs mu hindex (chi • omega)
  exact map_discreteSeriesOrbitMeasure_baseChange _ _ _ mu omega chi lambda

/-- Nonnegative integration in actual rational-point character parameters. -/
theorem lintegral_rationalDiscreteSeriesOrbitMeasure :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (lambda : Measure (unitaryUnramifiedCharacters
        (fun psi => (rationalNormCharacters G psi).toMul)))
      (f : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega → ℝ≥0∞),
      Measurable f →
        ∫⁻ eta, f eta ∂rationalDiscreteSeriesOrbitMeasure s hs mu hindex omega lambda =
          (Nat.card (discreteSeriesStabilizer (GroupScheme.rationalPoints.map s).range
            hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega) : ℝ≥0∞)⁻¹ *
            ∫⁻ chi, f (discreteSeriesOrbitMap (GroupScheme.rationalPoints.map s).range
              hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega chi)
              ∂lambda := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega lambda f hf
  let := finite_rationalDiscreteSeriesStabilizer s hs mu hindex omega
  exact lintegral_discreteSeriesOrbitMeasure _ _ _ mu omega lambda f hf

end Langlands.Plancherel
