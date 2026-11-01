import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedGLFourier
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonWeightedSynthesis
import Mathlib.MeasureTheory.Group.Prod

/-! Exact subgroup Haar shear and the actual signed original Fourier kernel. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis GeneralLinear Whittaker
open CompactWhittakerSynthesis

universe uG uF

section General

variable {G : Type uG} [Group G] [MeasurableSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]
  (H : Subgroup G) [MeasurableSpace H]
  (hH : Measurable (Subtype.val : H → G))

/-- Multiplying the ambient coordinate by the subgroup coordinate, with its
actual inverse, gives a measurable equivalence. -/
def subgroupLeftHaarShear : H × G ≃ᵐ H × G where
  toEquiv := .prodShear (.refl H) (fun h => .mulLeft (h : G))
  measurable_toFun :=
    measurable_fst.prodMk ((hH.comp measurable_fst).mul measurable_snd)
  measurable_invFun :=
    measurable_fst.prodMk ((hH.comp measurable_fst).inv.mul measurable_snd)

@[simp] theorem subgroupLeftHaarShear_apply (z : H × G) :
    subgroupLeftHaarShear H hH z = (z.1, z.1.val * z.2) := rfl

/-- Only left invariance of the ambient measure is needed; the subgroup
coordinate and its measure remain unchanged. -/
theorem measurePreserving_subgroupLeftHaarShear
    (μH : Measure H) (μG : Measure G) [SFinite μH] [SFinite μG]
    [Measure.IsMulLeftInvariant μG] :
    MeasurePreserving (subgroupLeftHaarShear H hH) (μH.prod μG) (μH.prod μG) :=
  (MeasurePreserving.id μH).skew_product
    ((hH.comp measurable_fst).mul measurable_snd)
    (Filter.Eventually.of_forall fun h => map_mul_left_eq_self μG h.val)

/-- The shear preserves genuine absolute convergence in both directions. -/
theorem integrable_subgroupLeftHaarShear_iff
    (μH : Measure H) (μG : Measure G) [SFinite μH] [SFinite μG]
    [Measure.IsMulLeftInvariant μG] (f : H × G → ℂ) :
    Integrable (fun z => f (subgroupLeftHaarShear H hH z)) (μH.prod μG) ↔
      Integrable f (μH.prod μG) :=
  (measurePreserving_subgroupLeftHaarShear H hH μH μG).integrable_comp_emb
    (subgroupLeftHaarShear H hH).measurableEmbedding

/-- Exact transport of the total Bochner integral introduces no scalar. -/
theorem integral_subgroupLeftHaarShear
    (μH : Measure H) (μG : Measure G) [SFinite μH] [SFinite μG]
    [Measure.IsMulLeftInvariant μG] (f : H × G → ℂ) :
    (∫ z, f (subgroupLeftHaarShear H hH z) ∂μH.prod μG) =
      ∫ z, f z ∂μH.prod μG :=
  (measurePreserving_subgroupLeftHaarShear H hH μH μG).integral_comp'
    f

end General

namespace GLDeterminantDensity

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance haarShearTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance haarShearValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance haarShearLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance haarShearT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance haarShearSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance haarShearMeasurable : MeasurableSpace F.Carrier := borel _
local instance haarShearBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance haarShearGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance haarShearGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance haarShearGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
local instance haarShearGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
local instance haarShearNLocallyCompact (n : ℕ) :
    LocallyCompactSpace (upperUnipotent (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.upperUnipotentLocallyCompactSpace (n + 1)
local instance haarShearNSecondCountable (n : ℕ) :
    SecondCountableTopology (upperUnipotent (n + 1) F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance haarShearNMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance haarShearNBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩

local instance haarShearTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

/-- The signed original kernel after the exact substitution `X = u g`. -/
def signedUnipotentGeneralLinearFourierShearedKernel
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (z : upperUnipotent (n + 1) F.Carrier ×
      Langlands.GeneralLinear (n + 1) F.Carrier) : ℂ :=
  determinantWeight abv z.2 (n + 1 : ℕ) *
    ((inverseStandardCharacter ψ n z.1 : ℂ) * Φ (z.1.val * z.2).val *
      rectangularFourierIntegral ψ ν Ψ (rankOneSignedWeyl n * z.2).val)

/-- Unipotent determinant one removes the weight change, and the true
group substitution cancels `u⁻¹ u` in the signed Weyl Fourier argument. -/
theorem signedUnipotentGeneralLinearFourierOriginalKernel_shear
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (z : upperUnipotent (n + 1) F.Carrier ×
      Langlands.GeneralLinear (n + 1) F.Carrier) :
    signedUnipotentGeneralLinearFourierOriginalKernel F ψ ν n Φ Ψ
      (subgroupLeftHaarShear (upperUnipotent (n + 1) F.Carrier)
        continuous_subtype_val.measurable z) =
      signedUnipotentGeneralLinearFourierShearedKernel F ψ ν n Φ Ψ z := by
  have hw : determinantWeight abv (z.1.val * z.2) (n + 1 : ℕ) =
      determinantWeight abv z.2 (n + 1 : ℕ) := by
    change (Shahidi.determinantPower abv (n + 1) (n + 1 : ℕ) (z.1.val * z.2) : ℂ) = _
    rw [map_mul, determinantPower_upperUnipotent, one_mul]
    rfl
  simp only [signedUnipotentGeneralLinearFourierOriginalKernel,
    signedUnipotentMatrixFourierOriginalKernel, subgroupLeftHaarShear_apply,
    signedUnipotentGeneralLinearFourierShearedKernel, hw]
  congr 3
  rw [← Units.val_mul, mul_assoc, inv_mul_cancel_left]

/-- Genuine product convergence transfers through the Haar shear. -/
theorem integrable_generalLinear_signedUnipotentMatrixFourierShearedKernel
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (hΦ : tsupport (Φ : _ → ℂ) ⊆
      Set.range (Units.val : Langlands.GeneralLinear (n + 1) F.Carrier →
        Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) :
    Integrable (signedUnipotentGeneralLinearFourierShearedKernel F ψ ν n Φ Ψ)
      ((unipotentHaar F.Carrier n).prod (generalLinearHaar F.Carrier n)) := by
  have hi := (integrable_subgroupLeftHaarShear_iff
    (upperUnipotent (n + 1) F.Carrier) continuous_subtype_val.measurable
    (unipotentHaar F.Carrier n) (generalLinearHaar F.Carrier n)
    (signedUnipotentGeneralLinearFourierOriginalKernel F ψ ν n Φ Ψ)).2
    (integrable_generalLinear_signedUnipotentMatrixFourierOriginalKernel F ψ ν hsd n Φ Ψ hΦ)
  simpa only [signedUnipotentGeneralLinearFourierOriginalKernel_shear] using hi

/-- The original and sheared product integrals are exactly equal, including
as total integrals when no convergence premise is supplied. -/
theorem integral_generalLinear_signedUnipotentMatrixFourierShearedKernel
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) :
    (∫ z, signedUnipotentGeneralLinearFourierShearedKernel F ψ ν n Φ Ψ z
      ∂(unipotentHaar F.Carrier n).prod (generalLinearHaar F.Carrier n)) =
    ∫ z, signedUnipotentGeneralLinearFourierOriginalKernel F ψ ν n Φ Ψ z
      ∂(unipotentHaar F.Carrier n).prod (generalLinearHaar F.Carrier n) := by
  simpa only [signedUnipotentGeneralLinearFourierOriginalKernel_shear] using
    integral_subgroupLeftHaarShear
      (upperUnipotent (n + 1) F.Carrier) continuous_subtype_val.measurable
      (unipotentHaar F.Carrier n) (generalLinearHaar F.Carrier n)
      (signedUnipotentGeneralLinearFourierOriginalKernel F ψ ν n Φ Ψ)

end GLDeterminantDensity
end Langlands.RankinSelberg
