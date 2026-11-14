import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockMeasurePackage
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockMeasureTransport
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockNormalization
/-!
# Common measure package for the linked lower mixed quotient identities

The normalized subgroup measures admit all four required compatible quotients.
Every compatible choice is sigma-finite, including its prescribed lower transport.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
open Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient hiding CompatibleExistenceStatement CompatibleFinitenessStatement LowerMixedQuotient MeasurePackageStatement compatibleExistence compatibleFiniteness compatibleQuotient_sigmaFinite continuous_determinantOrder continuous_firstBlockFiberPoint continuous_projectionFromLower continuous_projectionFromMixed continuous_radicalFiberPoint determinantOrder determinantOrder_mk determinantOrder_projectionFromLower determinantOrder_projectionFromMixed determinantOrder_radicalFiberPoint determinantSlice firstBlockAverage firstBlockAverage_mk firstBlockEmbedding_mul_lowerRadical_mul_mixedEmbedding firstBlockFiberIntegral firstBlockFiberIntegral_def firstBlockFiberIntegral_lowerMixedSubgroup_mul firstBlockFiberIntegral_lowerRadical_mixedEmbedding_mul firstBlockFiberPoint firstBlockFiberPoint_lowerRadical_mixedEmbedding_mul firstBlockFiberPoint_mk integral_comp_radicalChange isClopen_determinantSlice isClosed_lowerMixedSubgroup lowerBlockUnipotent_le_lowerMixedSubgroup lowerHaar lowerHaar_isHaar lowerHaar_isMulRightInvariant lowerHaar_regular lowerMeasurePackageInstance01 lowerMeasurePackageInstance02 lowerMeasurePackageInstance03 lowerMeasurePackageInstance04 lowerMeasurePackageInstance08 lowerMeasurePackageInstance09 lowerMeasurePackageInstance10 lowerMeasurePackageInstance11 lowerMeasurePackageInstance12 lowerMeasurePackageInstance13 lowerMeasurePackageInstance14 lowerMeasurePackageInstance21 lowerMeasurePackageInstance22 lowerMeasurePackageInstance25 lowerMeasurePackageInstance26 lowerMeasurePackageInstance29 lowerMeasurePackageInstance30 lowerMeasurePackageInstance31 lowerMeasurePackageInstance32 lowerMeasurePackageInstance33 lowerMeasurePackageInstance34 lowerMeasurePackageInstance35 lowerMeasurePackageInstance36 lowerMeasurePackageInstance37 lowerMeasureTransportInstance01 lowerMeasureTransportInstance02 lowerMeasureTransportInstance03 lowerMeasureTransportInstance04 lowerMeasureTransportInstance08 lowerMeasureTransportInstance09 lowerMeasureTransportInstance10 lowerMeasureTransportInstance11 lowerMeasureTransportInstance12 lowerMeasureTransportInstance13 lowerMeasureTransportInstance14 lowerMeasureTransportInstance17 lowerMeasureTransportInstance18 lowerMeasureTransportInstance21 lowerMeasureTransportInstance22 lowerMeasureTransportInstance23 lowerMeasureTransportInstance24 lowerMeasure_isCompatible lowerMeasure_sigmaFinite lowerMeasuresInstance01 lowerMeasuresInstance02 lowerMeasuresInstance03 lowerMeasuresInstance04 lowerMeasuresInstance05 lowerMeasuresInstance06 lowerMeasuresInstance07 lowerMeasuresInstance08 lowerMeasuresInstance09 lowerMeasuresInstance10 lowerMeasuresInstance13 lowerMeasuresInstance14 lowerMeasuresInstance15 lowerMeasuresInstance16 lowerMeasuresInstance17 lowerMeasuresInstance18 lowerMeasuresInstance19 lowerMeasuresInstance20 lowerMeasuresInstance21 lowerMeasuresInstance22 lowerMeasuresInstance23 lowerMeasuresInstance24 lowerMixedCoordinates lowerMixedCoordinates_lowerProduct lowerMixedDiagonal lowerMixedDiagonal_fst_val lowerMixedDiagonal_lowerProduct lowerMixedDiagonal_snd_val lowerMixedHaar lowerMixedHaar_integral lowerMixedHaar_isHaar lowerMixedHaar_isMulRightInvariant lowerMixedHaar_regular lowerMixedIntegralOpen lowerMixedIntegralOpen_isCompact lowerMixedProductMeasure lowerMixedProductMeasure_eq_smul lowerMixedProductMeasure_isHaar lowerMixedProductMeasure_isMulLeftInvariant lowerMixedProductMeasure_isMulRightInvariant lowerMixedSubgroup lowerMixedSubgroupEquiv lowerMixedSubgroupEquiv_apply_val lowerMixedSubgroupEquiv_mul lowerMixedSubgroupEquiv_symm_apply_fst lowerMixedSubgroupHomeomorph lowerMixedSubgroup_le_normOneSubgroup lowerMixedSubgroup_le_oppositeParabolic lowerMixed_compatibleMeasureExists lowerMixed_decomposition lowerMixed_preimage_integral lowerNormalizationInstance01 lowerNormalizationInstance02 lowerNormalizationInstance03 lowerNormalizationInstance04 lowerNormalizationInstance05 lowerNormalizationInstance06 lowerNormalizationInstance07 lowerNormalizationInstance08 lowerNormalizationInstance10 lowerNormalizationInstance11 lowerNormalizationInstance12 lowerNormalizationInstance13 lowerNormalizationInstance14 lowerNormalizationInstance15 lowerNormalizationInstance16 lowerNormalizationInstance17 lowerNormalizationInstance18 lowerNormalizationInstance19 lowerNormalizationInstance20 lowerNormalizationInstance21 lowerNormalizationInstance22 lowerNormalizationInstance23 lowerNormalizationInstance24 lowerNormalizationInstance25 lowerNormalizationInstance26 lowerProduct_lowerMixedCoordinates lowerProduct_mem lowerRadical_mul_leviEmbedding_one_mem measurableSet_determinantSlice measurePackage measurePreserving_radicalChange mem_lowerMixedSubgroup_iff mixedSubgroup_le_lowerMixedSubgroup mk_mem_determinantSlice normOneHaar_integral projectionFromLower projectionFromLower_mk projectionFromLower_preimage_determinantSlice projectionFromMixed projectionFromMixed_mk projectionFromMixed_preimage_determinantSlice quotientAverage_lower_transport radicalAverage radicalAverage_mk radicalChange radicalChangeHomeomorph radicalChangeHomeomorph_apply radicalChange_apply radicalFiberIntegral radicalFiberIntegral_def radicalFiberIntegral_lowerMixedSubgroup_mul radicalFiberIntegral_lowerRadical_mixedEmbedding_mul radicalFiberPoint radicalFiberPoint_def radicalFiberPoint_lowerRadical_mixedEmbedding_mul radicalFiberPoint_mem_determinantSlice_iff
open Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockFirstBlockQuotient hiding MixedQuotient NormOneRightInvariant blockUnipotent_le_mixedSubgroup continuous_determinantOrder continuous_fiberPoint determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice determinant_mixedEmbedding fiberIntegral fiberIntegral_def fiberIntegral_mixedEmbedding_mul fiberIntegral_mixedSubgroup_mul fiberPoint_mem_determinantSlice_iff fiberPoint_mixedEmbedding_mul firstBlockAverage firstBlockAverage_mk firstBlockAverage_rightTranslate instBorelSpaceGeneralLinearCarrier instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instIsNonarchimedeanLocalFieldCarrier instLocallyCompactSpaceMatrixFinCarrier instLocallyCompactSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instLocallyCompactSpaceSubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceGeneralLinearCarrier instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instSecondCountableTopologyGeneralLinearCarrier instSecondCountableTopologySubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instSecondCountableTopologySubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instT2SpaceCarrier instTopologicalSpaceCarrier instValuativeRelCarrier isClopen_determinantSlice isClosed_mixedSubgroup isOpenEmbedding_normOneSubtype map_normOneHaar measurableSet_determinantSlice mem_determinantSlice mem_mixedSubgroup_iff mem_mixedSubgroup_iff_determinantNorm mem_normOneSubgroup_iff mem_normOneSubgroup_iff_normalizedAbs mixedCoordinates mixedCoordinates_mixedEmbedding mixedEmbedding mixedEmbedding_apply mixedEmbedding_index_one_one mixedEmbedding_index_one_zero mixedEmbedding_index_zero_one mixedEmbedding_index_zero_zero mixedEmbedding_mem mixedEmbedding_mixedCoordinates mixedHaar mixedHaar_isHaar mixedHaar_isMulRightInvariant mixedHaar_regular mixedSubgroup mixedSubgroupEquiv mixedSubgroupEquiv_apply_val mixedSubgroupHomeomorph mixedSubgroup_le_normOneSubgroup mixedSubgroup_le_parabolic mixed_compatibleMeasureExists mk_mem_determinantSlice normOneHaar normOneHaar_isHaar normOneHaar_isMulRightInvariant normOneHaar_regular normOneRightInvariant_of_isCompatible normOneSubgroup ord_determinant_eq_zero rightTranslate_mem_determinantSlice
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice firstBlockAverage firstBlockAverage_mk isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice

universe uF

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance lowerMeasurePackageInstance04 : T2Space F :=
  (⟨⟩ : LocalFieldData F).fieldT2
local instance lowerMeasurePackageInstance08 (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup n
local instance lowerMeasurePackageInstance09 (n : ℕ) :
    MeasurableSpace (GeneralLinear n F) := borel _
local instance lowerMeasurePackageInstance10 (n : ℕ) :
    BorelSpace (GeneralLinear n F) := ⟨rfl⟩
local instance lowerMeasurePackageInstance11 (n : ℕ) :
    SecondCountableTopology (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology n
local instance lowerMeasurePackageInstance12 (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace n
local instance lowerMeasurePackageInstance13 (n : ℕ) :
    MeasurableSpace (upperUnipotent n F) := borel _
local instance lowerMeasurePackageInstance14 (n : ℕ) :
    BorelSpace (upperUnipotent n F) := ⟨rfl⟩
local instance lowerMeasurePackageInstance21 :
    MeasurableSpace (mixedSubgroup F h) := borel _
local instance lowerMeasurePackageInstance22 :
    BorelSpace (mixedSubgroup F h) := ⟨rfl⟩
local instance lowerMeasurePackageInstance25 :
    MeasurableSpace (lowerMixedSubgroup F h) := borel _
local instance lowerMeasurePackageInstance26 :
    BorelSpace (lowerMixedSubgroup F h) := ⟨rfl⟩
local instance lowerMeasurePackageInstance29 :
    MeasurableSpace (LowerMixedQuotient F h) := borel _
local instance lowerMeasurePackageInstance30 :
    BorelSpace (LowerMixedQuotient F h) := ⟨rfl⟩
local instance lowerMeasurePackageInstance31 :
    MeasurableSpace (MixedQuotient F h) := borel _
local instance lowerMeasurePackageInstance32 :
    BorelSpace (MixedQuotient F h) := ⟨rfl⟩
local instance lowerMeasurePackageInstance33 (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F) := borel _
local instance lowerMeasurePackageInstance34 (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
local instance lowerMeasurePackageInstance35 :
    MeasurableSpace (lowerBlockUnipotent h F) := borel _
local instance lowerMeasurePackageInstance36 :
    BorelSpace (lowerBlockUnipotent h F) := ⟨rfl⟩
local instance lowerMeasurePackageInstance37 :
    MeasurableSpace (LowerQuotient h F) := borel _

/-- Regular compatible measures on the closed quotients at hand are sigma-finite. -/
theorem compatibleQuotient_sigmaFinite
    (n : ℕ) (H : Subgroup (GeneralLinear (n + 1) F))
    (hH : IsClosed (H : Set (GeneralLinear (n + 1) F)))
    [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
    (μH : Measure H) [μH.IsMulRightInvariant]
    (ν : Measure (LeftQuotient H))
    (hν : IsCompatible H (generalLinearHaar F n) μH ν) :
    SigmaFinite ν := by
  have : ν.Regular := hν.regular
  have : T2Space (LeftQuotient H) := leftQuotient_t2Space H hH
  have : LocallyCompactSpace (LeftQuotient H) := leftQuotient_locallyCompactSpace H
  have : SecondCountableTopology (LeftQuotient H) :=
    Topology.IsOpenQuotientMap.secondCountableTopology (leftQuotient_isOpenQuotientMap H)
  infer_instance

/-- The four prescribed standard and mixed quotient measures exist. -/
abbrev CompatibleExistenceStatement : Prop :=
  CompatibleMeasureExists (upperUnipotent (m 0 + 1) F)
    (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) ∧
  CompatibleMeasureExists (mixedSubgroup F h)
    (generalLinearHaar F t) (mixedHaar F h) ∧
  CompatibleMeasureExists (lowerMixedSubgroup F h)
    (generalLinearHaar F t) (lowerMixedHaar F h) ∧
  CompatibleMeasureExists (upperUnipotent (t + 1) F)
    (generalLinearHaar F t) (unipotentHaar F t)

/-- Existence uses the fixed measures, independently of every rectangular Haar. -/
theorem compatibleExistence : CompatibleExistenceStatement F h :=
  ⟨TwoBlockUnipotentQuotient.fullUnipotent_compatibleMeasureExists F (m 0),
    mixed_compatibleMeasureExists F h, lowerMixed_compatibleMeasureExists F h,
    TwoBlockUnipotentQuotient.fullUnipotent_compatibleMeasureExists F t⟩

/-- Every compatible choice has the required finiteness and exact lower transport. -/
abbrev CompatibleFinitenessStatement : Prop :=
  ∀ (νA : Measure (LeftUnipotentQuotient (m 0) F))
    (νM : Measure (MixedQuotient F h))
    (νL : Measure (LowerMixedQuotient F h))
    (νN : Measure (LeftUnipotentQuotient t F)),
    IsCompatible (upperUnipotent (m 0 + 1) F)
      (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) νA →
    IsCompatible (mixedSubgroup F h)
      (generalLinearHaar F t) (mixedHaar F h) νM →
    IsCompatible (lowerMixedSubgroup F h)
      (generalLinearHaar F t) (lowerMixedHaar F h) νL →
    IsCompatible (upperUnipotent (t + 1) F)
      (generalLinearHaar F t) (unipotentHaar F t) νN →
    SigmaFinite νA ∧ SigmaFinite νM ∧ SigmaFinite νL ∧ SigmaFinite νN ∧
    IsCompatible (lowerBlockUnipotent h F)
      (generalLinearHaar F t) (lowerHaar F h)
      (Measure.map (lowerToStandard h F).symm νN) ∧
    SigmaFinite (Measure.map (lowerToStandard h F).symm νN)

/-- Regularity on the second-countable locally compact closed quotients proves
sigma-finiteness; inverse conjugation and inverse left translation give compatibility. -/
theorem compatibleFiniteness : CompatibleFinitenessStatement F h := by
  intro νA νM νL νN hA hM hL hN
  have hσN := lowerMeasure_sigmaFinite F h νN hN
  exact ⟨compatibleQuotient_sigmaFinite F (m 0) _
      (UpperUnipotent.isClosed (R := F)) _ νA hA,
    compatibleQuotient_sigmaFinite F t _ (isClosed_mixedSubgroup F h) _ νM hM,
    compatibleQuotient_sigmaFinite F t _ (isClosed_lowerMixedSubgroup F h) _ νL hL,
    hσN.1, lowerMeasure_isCompatible F h νN hN, hσN.2⟩

/-- The common existence, compatibility and sigma-finiteness package. -/
abbrev MeasurePackageStatement : Prop :=
  CompatibleExistenceStatement F h ∧ CompatibleFinitenessStatement F h

theorem measurePackage : MeasurePackageStatement F h :=
  ⟨compatibleExistence F h, compatibleFiniteness F h⟩

end Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
