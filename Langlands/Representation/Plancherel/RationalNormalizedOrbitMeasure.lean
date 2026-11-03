import Langlands.Representation.Plancherel.RationalCharacterHaar
import Langlands.Representation.Plancherel.RationalDiscreteSeriesOrbitMeasure

/-! # Discrete-series orbit measures with the I.1 character scale -/

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

local instance rationalNormalizedOrbitGroupPointTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X
local instance rationalNormalizedOrbitNonarchimedeanGroup :
    NonarchimedeanGroup (GroupScheme.rationalPoints G) :=
  rationalPoints_nonarchimedeanGroup G

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
variable (s : T.toGrp ⟶ G) (hs : GroupScheme.IsCentral s)
variable [MeasurableSpace (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range)]
variable (mu : Measure (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range))
variable (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)

/-- The actual orbit measure with the character measure fixed by restriction
kernel cardinality, rather than a freely supplied character measure. -/
def rationalNormalizedDiscreteSeriesOrbitMeasure :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
      Measure (discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
        (fun psi => (rationalNormCharacters G psi).toMul) omega) := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega
  exact rationalDiscreteSeriesOrbitMeasure s hs mu hindex omega
    (rationalUnitaryUnramifiedCharacterHaar s hs hindex)

/-- Comparison to probability character parameters records both finite-fiber
factors. It does not impose probability normalization on the orbit. -/
theorem rationalNormalizedDiscreteSeriesOrbitMeasure_eq_smul_probability :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
      rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega =
        (Nat.card (rationalUnitaryUnramifiedCharacterRestrict s).toMonoidHom.ker : ℝ≥0∞) •
          rationalDiscreteSeriesOrbitMeasure s hs mu hindex omega
            (rationalUnitaryUnramifiedProbabilityHaar G) := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega
  unfold rationalNormalizedDiscreteSeriesOrbitMeasure
  rw [rationalUnitaryUnramifiedCharacterHaar_eq_smul_probability,
    rationalDiscreteSeriesOrbitMeasure_smul]

@[simp]
theorem rationalNormalizedDiscreteSeriesOrbitMeasure_apply :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (E : Set (discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega)),
      MeasurableSet E → rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega E =
        ((Nat.card (rationalUnitaryUnramifiedCharacterRestrict s).toMonoidHom.ker : ℝ≥0∞) /
          (Nat.card (discreteSeriesStabilizer (GroupScheme.rationalPoints.map s).range
            hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega) : ℝ≥0∞)) *
          rationalUnitaryUnramifiedProbabilityHaar G
            (discreteSeriesOrbitMap (GroupScheme.rationalPoints.map s).range
              hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega ⁻¹' E) := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega E hE
  unfold rationalNormalizedDiscreteSeriesOrbitMeasure
  rw [rationalDiscreteSeriesOrbitMeasure_apply s hs mu hindex omega _ E hE,
    rationalUnitaryUnramifiedCharacterHaar_apply]
  simp only [div_eq_mul_inv, mul_assoc]
  rw [mul_left_comm]

@[simp]
theorem rationalNormalizedDiscreteSeriesOrbitMeasure_univ :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
      rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega Set.univ =
        (Nat.card (rationalUnitaryUnramifiedCharacterRestrict s).toMonoidHom.ker : ℝ≥0∞) /
          (Nat.card (discreteSeriesStabilizer (GroupScheme.rationalPoints.map s).range
            hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega) : ℝ≥0∞) := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega
  rw [rationalNormalizedDiscreteSeriesOrbitMeasure_apply s hs mu hindex omega _ MeasurableSet.univ]
  simp

/-- The actual twisting map locally preserves the fixed I.1 character measure.
Its left invariance and finite stabilizer are derived. -/
theorem isLocallyMeasurePreserving_rationalNormalizedDiscreteSeriesOrbitMap :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
      IsLocallyMeasurePreserving
        (discreteSeriesOrbitMap (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega)
        (rationalUnitaryUnramifiedCharacterHaar s hs hindex)
        (rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega) := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega
  exact isLocallyMeasurePreserving_rationalDiscreteSeriesOrbitMap s hs mu hindex omega
    (rationalUnitaryUnramifiedCharacterHaar s hs hindex)

/-- The identity on represented classes preserves the fixed-scale orbit measure
when the base class is changed by a unitary unramified twist. -/
theorem map_rationalNormalizedDiscreteSeriesOrbitMeasure_baseChange :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (chi : unitaryUnramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul)),
      Measure.map (discreteSeriesOrbitBaseChange (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega chi)
        (rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex (chi • omega)) =
          rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega chi
  exact map_rationalDiscreteSeriesOrbitMeasure_baseChange s hs mu hindex omega chi
    (rationalUnitaryUnramifiedCharacterHaar s hs hindex)

/-- Nonnegative integration with the I.1 character measure, permitting infinite
values. No complex integrability conclusion is asserted. -/
theorem lintegral_rationalNormalizedDiscreteSeriesOrbitMeasure :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (f : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega → ℝ≥0∞),
      Measurable f →
        ∫⁻ eta, f eta ∂rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega =
          (Nat.card (discreteSeriesStabilizer (GroupScheme.rationalPoints.map s).range
            hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega) : ℝ≥0∞)⁻¹ *
            ∫⁻ chi, f (discreteSeriesOrbitMap (GroupScheme.rationalPoints.map s).range
              hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega chi)
              ∂rationalUnitaryUnramifiedCharacterHaar s hs hindex := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega f hf
  exact lintegral_rationalDiscreteSeriesOrbitMeasure s hs mu hindex omega
    (rationalUnitaryUnramifiedCharacterHaar s hs hindex) f hf

/-- The same formula in probability character parameters displays the exact
restriction-kernel to stabilizer ratio. -/
theorem lintegral_rationalNormalizedDiscreteSeriesOrbitMeasure_probability :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (f : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega → ℝ≥0∞),
      Measurable f →
        ∫⁻ eta, f eta ∂rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega =
          ((Nat.card (rationalUnitaryUnramifiedCharacterRestrict s).toMonoidHom.ker : ℝ≥0∞) /
            (Nat.card (discreteSeriesStabilizer (GroupScheme.rationalPoints.map s).range
              hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega) : ℝ≥0∞)) *
            ∫⁻ chi, f (discreteSeriesOrbitMap (GroupScheme.rationalPoints.map s).range
              hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega chi)
              ∂rationalUnitaryUnramifiedProbabilityHaar G := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega f hf
  rw [lintegral_rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega f hf,
    rationalUnitaryUnramifiedCharacterHaar_eq_smul_probability, lintegral_smul_measure]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_assoc]
  rw [mul_left_comm]

end Langlands.Plancherel
