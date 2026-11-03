import Langlands.Representation.Plancherel.RationalNormalizedOrbitMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! # Convergent integration on actual discrete-series twist orbits -/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology MeasureTheory
open Langlands.AlgebraicGeometry.PointTopology
open scoped ENNReal NNReal CategoryTheory.MonObj BoundedContinuousFunction

namespace Langlands.Plancherel

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance rationalOrbitIntegrationGroupPointTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X
local instance rationalOrbitIntegrationNonarchimedeanGroup :
    NonarchimedeanGroup (GroupScheme.rationalPoints G) :=
  rationalPoints_nonarchimedeanGroup G

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
variable (s : T.toGrp ⟶ G) (hs : GroupScheme.IsCentral s)

variable [MeasurableSpace (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range)]
variable (mu : Measure (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range))
variable (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)

instance isFiniteMeasure_rationalNormalizedDiscreteSeriesOrbitMeasure :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
      IsFiniteMeasure (rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega) := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega
  refine ⟨?_⟩
  rw [rationalNormalizedDiscreteSeriesOrbitMeasure_univ]
  let := finite_rationalDiscreteSeriesStabilizer s hs mu hindex omega
  exact ENNReal.div_lt_top (by simp) (by exact_mod_cast Nat.card_pos.ne')

theorem rationalNormalizedDiscreteSeriesOrbitMeasure_univ_pos :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
    0 < rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega Set.univ := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega
  rw [rationalNormalizedDiscreteSeriesOrbitMeasure_univ]
  let := finite_rationalUnitaryUnramifiedCharacterRestrict_ker s hs hindex
  exact ENNReal.div_pos_iff.mpr ⟨by exact_mod_cast Nat.card_pos.ne', by simp⟩

@[simp]
theorem rationalNormalizedDiscreteSeriesOrbitMeasure_real_univ :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
    (rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega).real Set.univ =
      (Nat.card (rationalUnitaryUnramifiedCharacterRestrict s).toMonoidHom.ker : ℝ) /
        (Nat.card (discreteSeriesStabilizer (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega) : ℝ) := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega
  simp [measureReal_def, ENNReal.toReal_div]

/-- Every continuous complex-valued function on the actual compact orbit is
integrable for its fixed character scale. -/
theorem integrable_rationalNormalizedDiscreteSeriesOrbitMeasure :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
    {f : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
      hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega → ℂ}
    (_hf : Continuous f),
    Integrable f (rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega) := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega f hf
  let := compactSpace_rationalDiscreteSeriesOrbit s hs mu omega
  exact (BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩).integrable _

/-- Actual Bochner integration, as a bounded complex linear functional on
bounded continuous orbit functions. Compactness covers every continuous function. -/
def rationalDiscreteSeriesOrbitIntegral :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
    (discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
      hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega →ᵇ ℂ) →L[ℂ] ℂ := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega
  exact LinearMap.mkContinuous
    { toFun := fun f => ∫ eta, f eta
        ∂rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega
      map_add' := fun f g => integral_add (f.integrable _) (g.integrable _)
      map_smul' := fun c f => by simpa using integral_smul c (fun eta => f eta) }
    ((rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega).real Set.univ)
    (fun f => f.norm_integral_le_mul_norm _)

@[simp]
theorem rationalDiscreteSeriesOrbitIntegral_apply :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
    (f : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
      hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega →ᵇ ℂ),
    rationalDiscreteSeriesOrbitIntegral s hs mu hindex omega f =
      ∫ eta, f eta ∂rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega f
  rfl

/-- The character pullback is integrable for both the fixed I.1 scale and
probability Haar, so both parameter formulas below are convergent integrals. -/
theorem integrable_rationalDiscreteSeriesOrbit_characterParameters :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (f : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega →ᵇ ℂ),
      Integrable (fun chi => f (discreteSeriesOrbitMap (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega chi))
        (rationalUnitaryUnramifiedCharacterHaar s hs hindex) ∧
      Integrable (fun chi => f (discreteSeriesOrbitMap (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega chi))
        (rationalUnitaryUnramifiedProbabilityHaar G) := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega f
  let := compactSpace_rationalUnitaryUnramifiedCharacters G
  let g := f.compContinuous ⟨discreteSeriesOrbitMap (GroupScheme.rationalPoints.map s).range
    hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega,
      continuous_discreteSeriesOrbitMap _ _ _ _ omega⟩
  exact ⟨g.integrable _, g.integrable _⟩

/-- The operator bound retains the exact source scale. -/
theorem norm_rationalDiscreteSeriesOrbitIntegral_le :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
    ‖rationalDiscreteSeriesOrbitIntegral s hs mu hindex omega‖ ≤
      (Nat.card (rationalUnitaryUnramifiedCharacterRestrict s).toMonoidHom.ker : ℝ) /
        (Nat.card (discreteSeriesStabilizer (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega) : ℝ) := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega
  rw [← rationalNormalizedDiscreteSeriesOrbitMeasure_real_univ s hs mu hindex omega]
  exact (rationalDiscreteSeriesOrbitIntegral s hs mu hindex omega).opNorm_le_bound
    ENNReal.toReal_nonneg (fun f => f.norm_integral_le_mul_norm _)

/-- Constants integrate to their value times the kernel-to-stabilizer mass. -/
@[simp]
theorem rationalDiscreteSeriesOrbitIntegral_const :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu) (c : ℂ),
    rationalDiscreteSeriesOrbitIntegral s hs mu hindex omega
      (BoundedContinuousFunction.const _ c) =
        ((Nat.card (rationalUnitaryUnramifiedCharacterRestrict s).toMonoidHom.ker : ℝ) /
          (Nat.card (discreteSeriesStabilizer (GroupScheme.rationalPoints.map s).range
            hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega) : ℝ)) • c := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega c
  simp

/-- Complex integration in the actual character parameters, with the finite
stabilizer factor and the fixed I.1 character measure. -/
theorem rationalDiscreteSeriesOrbitIntegral_eq_characterIntegral :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
    (f : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
      hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega →ᵇ ℂ),
    rationalDiscreteSeriesOrbitIntegral s hs mu hindex omega f =
      (Nat.card (discreteSeriesStabilizer (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega) : ℝ)⁻¹ •
        ∫ chi, f (discreteSeriesOrbitMap (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega chi)
          ∂rationalUnitaryUnramifiedCharacterHaar s hs hindex := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega f
  let := finite_rationalDiscreteSeriesStabilizer s hs mu hindex omega
  change (∫ eta, f eta ∂((Nat.card (discreteSeriesStabilizer
    (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
      (fun psi => (rationalNormCharacters G psi).toMul) omega) : ℝ≥0∞)⁻¹ •
        Measure.map (discreteSeriesOrbitMap (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega)
          (rationalUnitaryUnramifiedCharacterHaar s hs hindex))) = _
  rw [integral_smul_measure,
    integral_map_of_stronglyMeasurable
      (continuous_discreteSeriesOrbitMap _ _ _ _ omega).measurable
      f.continuous.measurable.stronglyMeasurable]
  simp

/-- The probability-parameter formula retains both finite-fiber factors. -/
theorem rationalDiscreteSeriesOrbitIntegral_eq_probabilityIntegral :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
    (f : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
      hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega →ᵇ ℂ),
    rationalDiscreteSeriesOrbitIntegral s hs mu hindex omega f =
      ((Nat.card (rationalUnitaryUnramifiedCharacterRestrict s).toMonoidHom.ker : ℝ) /
        (Nat.card (discreteSeriesStabilizer (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega) : ℝ)) •
        ∫ chi, f (discreteSeriesOrbitMap (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega chi)
          ∂rationalUnitaryUnramifiedProbabilityHaar G := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega f
  rw [rationalDiscreteSeriesOrbitIntegral_eq_characterIntegral,
    rationalUnitaryUnramifiedCharacterHaar_eq_smul_probability, integral_smul_measure]
  simp only [ENNReal.toReal_natCast, smul_smul, div_eq_mul_inv]
  rw [mul_comm]

/-- Integration is independent of the base class through the existing
identity-on-classes homeomorphism. -/
theorem rationalDiscreteSeriesOrbitIntegral_baseChange :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
    (chi : unitaryUnramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul))
    (f : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
      hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega →ᵇ ℂ),
    rationalDiscreteSeriesOrbitIntegral s hs mu hindex (chi • omega)
      (f.compContinuous ⟨discreteSeriesOrbitBaseChange (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega chi,
          (discreteSeriesOrbitBaseChange (GroupScheme.rationalPoints.map s).range
            hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega chi
              ).continuous⟩) =
      rationalDiscreteSeriesOrbitIntegral s hs mu hindex omega f := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega chi f
  simp only [rationalDiscreteSeriesOrbitIntegral_apply, BoundedContinuousFunction.compContinuous_apply]
  rw [← map_rationalNormalizedDiscreteSeriesOrbitMeasure_baseChange s hs mu hindex omega chi]
  exact (integral_map_of_stronglyMeasurable
    (discreteSeriesOrbitBaseChange _ _ _ _ omega chi).continuous.measurable
    f.continuous.measurable.stronglyMeasurable).symm

end Langlands.Plancherel
