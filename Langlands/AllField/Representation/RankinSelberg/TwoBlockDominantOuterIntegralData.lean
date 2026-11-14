import Langlands.Representation.RankinSelberg.TwoBlockDominantOuterIntegralData
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFixedSliceMeasureTransport
/-!
# Outer integrals for the strictly dominant rectangle kernel

This helper retains arbitrary functions on the actual lower quotient. It uses
exactly the existing lower transport of each supplied standard quotient measure.
The actual rectangle-integrated kernel, norm profile and fiber predicate are
supplied by `TwoBlockDominantQuotientKernelData`.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg.TwoBlockDominantRectangular hiding AbsoluteInput NormProfileIntegrable OuterIntegrable absoluteInput_standard_iff ae_lowerQuotientMeasure_iff integrable_lowerQuotientMeasure_iff outerFieldT2 outerFieldTopology outerFieldValuation outerGeneralLinearGroup outerGeneralLinearLocallyCompact outerGeneralLinearSecondCountable outerLocalField standardCompatible standardCompatible_sigmaFinite
open Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice

universe uF uE

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance outerFieldT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance outerGeneralLinearGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup n
local instance outerGeneralLinearLocallyCompact (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace n
local instance outerGeneralLinearSecondCountable (n : ℕ) :
    SecondCountableTopology (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology n

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable [MeasurableSpace (LeftUnipotentQuotient t F)]
  [BorelSpace (LeftUnipotentQuotient t F)]
variable [MeasurableSpace (LowerQuotient h F)]
  [BorelSpace (LowerQuotient h F)]

/-- Absolute integrability also transports in both directions, independently of
any identity of totalized integral values. -/
theorem integrable_lowerQuotientMeasure_iff
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (νN : Measure (LeftUnipotentQuotient t F))
    (K : LowerQuotient h F → E) :
    Integrable K (Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.lowerMeasure F h νN) ↔
      Integrable (fun q => K ((lowerToStandard h F).symm q)) νN :=
  integrable_map_equiv (canonicalLowerToStandardHomeomorph F h).symm.toMeasurableEquiv K

/-- Almost-everywhere fiber conditions transport for arbitrary predicates. -/
theorem ae_lowerQuotientMeasure_iff
    (νN : Measure (LeftUnipotentQuotient t F))
    (P : LowerQuotient h F → Prop) :
    (∀ᵐ q ∂Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.lowerMeasure F h νN, P q) ↔
      ∀ᵐ q ∂νN, P ((lowerToStandard h F).symm q) :=
  (canonicalLowerToStandardHomeomorph F h).symm.toMeasurableEquiv.measurableEmbedding.ae_map_iff

/-- Actual outer complex integrability, recorded as a condition, not inferred. -/
def OuterIntegrable (νN : Measure (LeftUnipotentQuotient t F))
    (K : LowerQuotient h F → ℂ) : Prop :=
  Integrable K (Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.lowerMeasure F h νN)

/-- Outer integrability of the supplied real norm profile. -/
def NormProfileIntegrable (νN : Measure (LeftUnipotentQuotient t F))
    (N : LowerQuotient h F → ℝ) : Prop :=
  Integrable N (Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.lowerMeasure F h νN)

/-- Conditions for an analytic successor: actual outer complex integrability,
outer integrability of the real norm profile, and almost-everywhere actual fiber
integrability. No clause is inferred from a totalized integral value. -/
def AbsoluteInput (νN : Measure (LeftUnipotentQuotient t F))
    (K : LowerQuotient h F → ℂ) (N : LowerQuotient h F → ℝ)
    (P : LowerQuotient h F → Prop) : Prop :=
  OuterIntegrable F h νN K ∧ NormProfileIntegrable F h νN N ∧
    ∀ᵐ q ∂Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.lowerMeasure F h νN, P q

/-- The full absolute-input condition written on the standard quotient. -/
theorem absoluteInput_standard_iff
    (νN : Measure (LeftUnipotentQuotient t F))
    (K : LowerQuotient h F → ℂ) (N : LowerQuotient h F → ℝ)
    (P : LowerQuotient h F → Prop) :
    AbsoluteInput F h νN K N P ↔
      Integrable (fun q => K ((lowerToStandard h F).symm q)) νN ∧
      Integrable (fun q => N ((lowerToStandard h F).symm q)) νN ∧
      ∀ᵐ q ∂νN, P ((lowerToStandard h F).symm q) := by
  unfold AbsoluteInput OuterIntegrable NormProfileIntegrable
  rw [integrable_lowerQuotientMeasure_iff, integrable_lowerQuotientMeasure_iff,
    ae_lowerQuotientMeasure_iff]

section Compatible

variable [MeasurableSpace (GeneralLinear (t + 1) F)]
  [BorelSpace (GeneralLinear (t + 1) F)]
variable [MeasurableSpace (upperUnipotent (t + 1) F)]
  [BorelSpace (upperUnipotent (t + 1) F)]

/-- Compatibility for every supplied right-invariance certificate and every
standard quotient measure, at the existing exact standard Haar normalizations. -/
def standardCompatible
    (hN : Measure.IsMulRightInvariant (unipotentHaar F t))
    (νN : Measure (LeftUnipotentQuotient t F)) : Prop :=
  letI := hN
  IsCompatible (upperUnipotent (t + 1) F)
    (generalLinearHaar F t) (unipotentHaar F t) νN

/-- Every compatible supplied standard measure and its prescribed lower measure
are sigma-finite. This selects no new measure or normalization. -/
theorem standardCompatible_sigmaFinite
    (hN : Measure.IsMulRightInvariant (unipotentHaar F t))
    (νN : Measure (LeftUnipotentQuotient t F))
    (hνN : standardCompatible F hN νN) :
    SigmaFinite νN ∧ SigmaFinite (Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.lowerMeasure F h νN) := by
  let := hN
  have : νN.Regular := hνN.regular
  have : T2Space (LeftUnipotentQuotient t F) :=
    leftQuotient_t2Space _ (UpperUnipotent.isClosed (R := F))
  have : LocallyCompactSpace (LeftUnipotentQuotient t F) :=
    leftQuotient_locallyCompactSpace _
  have : SecondCountableTopology (LeftUnipotentQuotient t F) :=
    Topology.IsOpenQuotientMap.secondCountableTopology (leftQuotient_isOpenQuotientMap _)
  have hσ : SigmaFinite νN := inferInstance
  exact ⟨hσ, (canonicalLowerToStandardHomeomorph F h).symm.toMeasurableEquiv.sigmaFinite_map⟩

end Compatible

end Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
