import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockRadicalAnalysis
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockRadicalTower
import Langlands.AllField.Representation.RankinSelberg.TwoBlockUnipotentQuotientAnalysis
/-!
# Analytic laws for the lower mixed radical tower

The exact zero-slice measure identity gives the Tonelli and Bochner laws for the
published unweighted average, together with genuine absolute integrability.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
open Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient hiding LowerMixedQuotient RadicalIntegrationStatement RadicalTowerStatement continuous_determinantOrder continuous_firstBlockFiberPoint continuous_lowerMixedFirstQuotient continuous_projectionFromLower continuous_projectionFromMixed continuous_radicalFiberPoint continuous_rightRadicalCoord determinantOrder determinantOrder_mk determinantOrder_projectionFromLower determinantOrder_projectionFromMixed determinantOrder_radicalFiberPoint determinantSlice firstBlockAverage firstBlockAverage_mk firstBlockEmbedding_mul_lowerRadical_mul_mixedEmbedding firstBlockFiberIntegral firstBlockFiberIntegral_def firstBlockFiberIntegral_lowerMixedSubgroup_mul firstBlockFiberIntegral_lowerRadical_mixedEmbedding_mul firstBlockFiberMeasures_lowerMixed_mul firstBlockFiberPoint firstBlockFiberPoint_lowerRadical_mixedEmbedding_mul firstBlockFiberPoint_mk firstBlockFiberPoint_slice_isCompact_preimage firstBlockKernel firstBlockKernel_compact_ne_top firstBlockKernel_isSFinite firstBlockKernel_mk instBorelSpaceCarrier instBorelSpaceCarrier_1 instBorelSpaceGeneralLinearCarrier instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceLeftUnipotentQuotientCarrier_1 instBorelSpaceLowerMixedQuotient instBorelSpaceLowerQuotientCarrier instBorelSpaceLowerQuotientCarrier_1 instBorelSpaceMixedQuotient instBorelSpaceMixedQuotient_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instLocallyCompactSpaceGeneralLinearCarrier instLocallyCompactSpaceGeneralLinearCarrier_1 instLocallyCompactSpaceMatrixFinCarrier instMeasurableSpaceCarrier instMeasurableSpaceCarrier_1 instMeasurableSpaceGeneralLinearCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier_1 instMeasurableSpaceLowerMixedQuotient instMeasurableSpaceLowerQuotientCarrier instMeasurableSpaceLowerQuotientCarrier_1 instMeasurableSpaceMixedQuotient instMeasurableSpaceMixedQuotient_1 instSecondCountableTopologyCarrier instSecondCountableTopologyCarrier_1 instSecondCountableTopologyGeneralLinearCarrier instSecondCountableTopologyGeneralLinearCarrier_1 instSecondCountableTopologyMatrixFinCarrier instT2SpaceCarrier instT2SpaceCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 integral_comp_radicalChange isClopen_determinantSlice isClosed_lowerMixedSubgroup lintegral_mixedHaar_radical lintegral_radicalFiberPoint_quotientAverageReal lintegral_radicalKernel_comp_quotientAverageReal lowerBlockUnipotent_le_lowerMixedSubgroup lowerMeasuresInstance01 lowerMeasuresInstance02 lowerMeasuresInstance03 lowerMeasuresInstance04 lowerMeasuresInstance05 lowerMeasuresInstance06 lowerMeasuresInstance07 lowerMeasuresInstance08 lowerMeasuresInstance09 lowerMeasuresInstance10 lowerMeasuresInstance13 lowerMeasuresInstance14 lowerMeasuresInstance15 lowerMeasuresInstance16 lowerMeasuresInstance17 lowerMeasuresInstance18 lowerMeasuresInstance19 lowerMeasuresInstance20 lowerMeasuresInstance21 lowerMeasuresInstance22 lowerMeasuresInstance23 lowerMeasuresInstance24 lowerMixedCoordinates lowerMixedCoordinates_lowerProduct lowerMixedDiagonal lowerMixedDiagonal_fst_val lowerMixedDiagonal_lowerProduct lowerMixedDiagonal_snd_val lowerMixedFirstQuotient lowerMixedFirstQuotient_lower_mul lowerMixedHaar lowerMixedHaar_integral lowerMixedHaar_isHaar lowerMixedHaar_isMulRightInvariant lowerMixedHaar_regular lowerMixedIntegralOpen lowerMixedIntegralOpen_isCompact lowerMixedProductMeasure lowerMixedProductMeasure_eq_smul lowerMixedProductMeasure_isHaar lowerMixedProductMeasure_isMulLeftInvariant lowerMixedProductMeasure_isMulRightInvariant lowerMixedSubgroup lowerMixedSubgroupEquiv lowerMixedSubgroupEquiv_apply_val lowerMixedSubgroupEquiv_mul lowerMixedSubgroupEquiv_symm_apply_fst lowerMixedSubgroupHomeomorph lowerMixedSubgroup_le_normOneSubgroup lowerMixedSubgroup_le_oppositeParabolic lowerMixed_compatibleMeasureExists lowerMixed_decomposition lowerMixed_preimage_integral lowerNormalizationInstance01 lowerNormalizationInstance02 lowerNormalizationInstance03 lowerNormalizationInstance04 lowerNormalizationInstance05 lowerNormalizationInstance06 lowerNormalizationInstance07 lowerNormalizationInstance08 lowerNormalizationInstance10 lowerNormalizationInstance11 lowerNormalizationInstance12 lowerNormalizationInstance13 lowerNormalizationInstance14 lowerNormalizationInstance15 lowerNormalizationInstance16 lowerNormalizationInstance17 lowerNormalizationInstance18 lowerNormalizationInstance19 lowerNormalizationInstance20 lowerNormalizationInstance21 lowerNormalizationInstance22 lowerNormalizationInstance23 lowerNormalizationInstance24 lowerNormalizationInstance25 lowerNormalizationInstance26 lowerProduct_lowerMixedCoordinates lowerProduct_mem lowerRadicalAnalysisInstance01 lowerRadicalAnalysisInstance02 lowerRadicalAnalysisInstance03 lowerRadicalAnalysisInstance05 lowerRadicalAnalysisInstance06 lowerRadicalAnalysisInstance07 lowerRadicalAnalysisInstance10 lowerRadicalAnalysisInstance11 lowerRadicalAnalysisInstance12 lowerRadicalAnalysisInstance23 lowerRadicalAnalysisInstance24 lowerRadicalAnalysisInstance27 lowerRadicalAnalysisInstance28 lowerRadicalAnalysisInstance31 lowerRadicalAnalysisInstance32 lowerRadicalAnalysisInstance36 lowerRadicalTowerInstance01 lowerRadicalTowerInstance02 lowerRadicalTowerInstance03 lowerRadicalTowerInstance04 lowerRadicalTowerInstance05 lowerRadicalTowerInstance06 lowerRadicalTowerInstance07 lowerRadicalTowerInstance08 lowerRadicalTowerInstance09 lowerRadicalTowerInstance10 lowerRadicalTowerInstance11 lowerRadicalTowerInstance12 lowerRadicalTowerInstance13 lowerRadicalTowerInstance14 lowerRadicalTowerInstance15 lowerRadicalTowerInstance16 lowerRadicalTowerInstance17 lowerRadicalTowerInstance18 lowerRadicalTowerInstance19 lowerRadicalTowerInstance20 lowerRadicalTowerInstance21 lowerRadicalTowerInstance22 lowerRadicalTowerInstance23 lowerRadicalTowerInstance24 lowerRadicalTowerInstance27 lowerRadicalTowerInstance28 lowerRadicalTowerInstance31 lowerRadicalTowerInstance32 lowerRadicalTowerInstance33 lowerRadicalTowerInstance34 lowerRadicalTowerInstance35 lowerRadicalTowerInstance36 lowerRadicalTowerInstance37 lowerRadical_mul_leviEmbedding_one_mem measurableSet_determinantSlice measurable_firstBlockFiberMeasures measurable_radicalFiberMeasures measurePreserving_radicalChange mem_lowerMixedSubgroup_iff mixedSubgroup_le_lowerMixedSubgroup mk_mem_determinantSlice normOneHaar_integral projectionFromLower projectionFromLower_mk projectionFromLower_preimage_determinantSlice projectionFromMixed projectionFromMixed_mk projectionFromMixed_preimage_determinantSlice radicalAverage radicalAverage_eq_integral_radicalKernel radicalAverage_mk radicalChange radicalChangeHomeomorph radicalChangeHomeomorph_apply radicalChange_apply radicalFiberIntegral radicalFiberIntegral_def radicalFiberIntegral_lowerMixedSubgroup_mul radicalFiberIntegral_lowerRadical_mixedEmbedding_mul radicalFiberMeasures_lowerMixed_mul radicalFiberPoint radicalFiberPoint_def radicalFiberPoint_isCompact_preimage radicalFiberPoint_lowerRadical_mixedEmbedding_mul radicalFiberPoint_mem_determinantSlice_iff radicalIntegration radicalKernel radicalKernel_comp radicalKernel_comp_restrict radicalKernel_compact_ne_top radicalKernel_isSFinite radicalKernel_mk radicalTower rightRadicalCoord rightRadicalCoord_mixed_mul_radical
open Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankLastRowReductionStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt TwoBlockUnipotentQuotientIntegrationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankLastRowReduction equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice

open _root_.MeasureTheory ProbabilityTheory
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockFirstBlockQuotient hiding MixedQuotient NormOneRightInvariant blockUnipotent_le_mixedSubgroup continuous_determinantOrder continuous_fiberPoint continuous_mixedFirstQuotient determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice determinant_mixedEmbedding fiberIntegral fiberIntegral_def fiberIntegral_mixedEmbedding_mul fiberIntegral_mixedSubgroup_mul fiberKernel fiberKernel_compact_ne_top fiberKernel_isSFinite fiberKernel_mk fiberMeasures_mixedSubgroup_mul fiberPoint_mem_determinantSlice_iff fiberPoint_mixedEmbedding_mul fiberPoint_slice_isCompact_preimage firstBlockAverage firstBlockAverage_mk firstBlockAverage_rightTranslate firstBlockEmbedding_mem_mixedSubgroup instBorelSpaceBlockQuotientCarrier instBorelSpaceBlockQuotientCarrier_1 instBorelSpaceGeneralLinearCarrier instBorelSpaceGeneralLinearCarrier_1 instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceLeftUnipotentQuotientCarrier_1 instBorelSpaceMixedQuotient instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instLocallyCompactSpaceGeneralLinearCarrier instLocallyCompactSpaceGeneralLinearCarrier_1 instLocallyCompactSpaceMatrixFinCarrier instLocallyCompactSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instLocallyCompactSpaceSubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceBlockQuotientCarrier instMeasurableSpaceBlockQuotientCarrier_1 instMeasurableSpaceGeneralLinearCarrier instMeasurableSpaceGeneralLinearCarrier_1 instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier_1 instMeasurableSpaceMixedQuotient instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instSecondCountableTopologyGeneralLinearCarrier instSecondCountableTopologyGeneralLinearCarrier_1 instSecondCountableTopologyGeneralLinearCarrier_2 instSecondCountableTopologySubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instSecondCountableTopologySubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instT2SpaceCarrier instT2SpaceCarrier_1 instT2SpaceCarrier_2 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 isClopen_determinantSlice isClosed_mixedSubgroup isOpenEmbedding_normOneSubtype map_normOneHaar map_restrict_smallSlice measurableSet_determinantSlice measurable_fiberMeasures mem_determinantSlice mem_mixedSubgroup_iff mem_mixedSubgroup_iff_determinantNorm mem_normOneSubgroup_iff mem_normOneSubgroup_iff_normalizedAbs mixedCoordinates mixedCoordinates_mixedEmbedding mixedEmbedding mixedEmbedding_apply mixedEmbedding_index_one_one mixedEmbedding_index_one_zero mixedEmbedding_index_zero_one mixedEmbedding_index_zero_zero mixedEmbedding_mem mixedEmbedding_mixedCoordinates mixedFirstQuotient mixedFirstQuotient_block_mul mixedHaar mixedHaar_isHaar mixedHaar_isMulRightInvariant mixedHaar_regular mixedSubgroup mixedSubgroupEquiv mixedSubgroupEquiv_apply_val mixedSubgroupHomeomorph mixedSubgroup_le_normOneSubgroup mixedSubgroup_le_parabolic mixed_compatibleMeasureExists mk_mem_determinantSlice mul_inv_mem_normOne_of_ord_eq normOneHaar normOneHaar_isHaar normOneHaar_isMulRightInvariant normOneHaar_regular normOneRightInvariant_of_isCompatible normOneSubgroup ord_determinant_eq_zero rightTranslate_mem_determinantSlice
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice firstBlockAverage firstBlockAverage_mk isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open scoped ENNReal CompactlySupported ProbabilityTheory

universe uF

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance lowerRadicalAnalysisInstance04 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance lowerRadicalAnalysisInstance05 : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance lowerRadicalAnalysisInstance06 : MeasurableSpace F := borel _
local instance lowerRadicalAnalysisInstance07 : BorelSpace F := ⟨rfl⟩
local instance lowerRadicalAnalysisInstance08 (a b : ℕ) : LocallyCompactSpace (Matrix (Fin b) (Fin a) F) :=
  inferInstanceAs (LocallyCompactSpace (Fin b → Fin a → F))
local instance lowerRadicalAnalysisInstance09 (a b : ℕ) : SecondCountableTopology (Matrix (Fin b) (Fin a) F) :=
  inferInstanceAs (SecondCountableTopology (Fin b → Fin a → F))
local instance lowerRadicalAnalysisInstance10 (n : ℕ) : IsTopologicalGroup (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup n
local instance lowerRadicalAnalysisInstance11 (n : ℕ) : MeasurableSpace (GeneralLinear n F) := borel _
local instance lowerRadicalAnalysisInstance12 (n : ℕ) : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
local instance lowerRadicalAnalysisInstance13 (n : ℕ) : SecondCountableTopology (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology n
local instance lowerRadicalAnalysisInstance14 (n : ℕ) : LocallyCompactSpace (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace n
local instance lowerRadicalAnalysisInstance15 (n : ℕ) : MeasurableSpace (normOneSubgroup F n) := borel _
local instance lowerRadicalAnalysisInstance16 (n : ℕ) : BorelSpace (normOneSubgroup F n) := ⟨rfl⟩
local instance lowerRadicalAnalysisInstance17 (n : ℕ) : SecondCountableTopology (normOneSubgroup F n) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerRadicalAnalysisInstance18 (n : ℕ) : LocallyCompactSpace (normOneSubgroup F n) :=
  (isOpenEmbedding_normOneSubtype F n).locallyCompactSpace
local instance lowerRadicalAnalysisInstance19 (n : ℕ) : MeasurableSpace (upperUnipotent n F) := borel _
local instance lowerRadicalAnalysisInstance20 (n : ℕ) : BorelSpace (upperUnipotent n F) := ⟨rfl⟩
local instance lowerRadicalAnalysisInstance21 (n : ℕ) : SecondCountableTopology (upperUnipotent n F) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerRadicalAnalysisInstance22 (n : ℕ) : LocallyCompactSpace (upperUnipotent n F) :=
  UpperUnipotent.locallyCompactSpace
local instance lowerRadicalAnalysisInstance23 : MeasurableSpace (lowerMixedSubgroup F h) := borel _
local instance lowerRadicalAnalysisInstance24 : BorelSpace (lowerMixedSubgroup F h) := ⟨rfl⟩
local instance lowerRadicalAnalysisInstance25 : SecondCountableTopology (lowerMixedSubgroup F h) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerRadicalAnalysisInstance26 : LocallyCompactSpace (lowerMixedSubgroup F h) :=
  (isClosed_lowerMixedSubgroup F h).locallyCompactSpace

local notation "R" => Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F
local notation "D" => normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F
local notation "μD" => Measure.prod (normOneHaar F (m 0)) (unipotentHaar F (m 1))

local instance lowerRadicalAnalysisInstance27 : MeasurableSpace (mixedSubgroup F h) := borel _
local instance lowerRadicalAnalysisInstance28 : BorelSpace (mixedSubgroup F h) := ⟨rfl⟩
local instance lowerRadicalAnalysisInstance29 : SecondCountableTopology (mixedSubgroup F h) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerRadicalAnalysisInstance30 : LocallyCompactSpace (mixedSubgroup F h) :=
  (isClosed_mixedSubgroup F h).locallyCompactSpace
local instance lowerRadicalAnalysisInstance31 : MeasurableSpace (MixedQuotient F h) := borel _
local instance lowerRadicalAnalysisInstance32 : BorelSpace (MixedQuotient F h) := ⟨rfl⟩
local instance lowerRadicalAnalysisInstance33 : T2Space (MixedQuotient F h) :=
  leftQuotient_t2Space _ (isClosed_mixedSubgroup F h)
local instance lowerRadicalAnalysisInstance34 : LocallyCompactSpace (MixedQuotient F h) := leftQuotient_locallyCompactSpace _
local instance lowerRadicalAnalysisInstance35 : SecondCountableTopology (MixedQuotient F h) :=
  Topology.IsOpenQuotientMap.secondCountableTopology (leftQuotient_isOpenQuotientMap _)
local instance lowerRadicalAnalysisInstance36 : MeasurableSpace (LowerMixedQuotient F h) := borel _
local instance lowerRadicalAnalysisInstance37 : BorelSpace (LowerMixedQuotient F h) := ⟨rfl⟩

local notation "O" => Valuation.integer (ValuativeRel.valuation F)

/-- The published unweighted radical average is the actual kernel integral
at every lower mixed quotient point. -/
theorem radicalAverage_eq_integral_radicalKernel
    (μR : Measure R) [μR.IsAddHaarMeasure]
    (f : MixedQuotient F h → ℂ) (hf : Measurable f) :
    radicalAverage F h μR f = fun q => ∫ z, f z ∂radicalKernel F h μR q := by
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    have hfm : Measurable (fun Z => radicalFiberPoint F h Z g) :=
      ((continuous_radicalFiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
    rw [radicalAverage_mk, radicalKernel_mk,
      integral_map hfm.aemeasurable hf.aestronglyMeasurable]

/-- The complete equation (2) conclusions on the required zero slices. -/
abbrev RadicalIntegrationStatement
    (μR : Measure R) [μR.IsAddHaarMeasure]
    (νL : Measure (LowerMixedQuotient F h)) (νM : Measure (MixedQuotient F h)) : Prop :=
  let c := μR {Z | ∀ i j, Z i j ∈ O}
  let νL0 := νL.restrict (determinantSlice F h 0)
  let νM0 := νM.restrict (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.determinantSlice F h 0)
  ∃ (κR : Kernel (LowerMixedQuotient F h) (MixedQuotient F h))
    (_hκR : IsSFiniteKernel κR),
    (∀ g : GeneralLinear (t + 1) F, κR (Quotient.mk _ g) =
      Measure.map (fun Z => radicalFiberPoint F h Z g) μR) ∧
    (κR ∘ₘ νL0 = c • νM0) ∧
    (∀ f : MixedQuotient F h → ℝ≥0∞, Measurable f →
      (∫⁻ q, ∫⁻ z, f z ∂κR q ∂νL0) = c * ∫⁻ z, f z ∂νM0) ∧
    (∀ f : MixedQuotient F h → ℂ, Measurable f →
      (Integrable f νM0 ↔
        (∀ᵐ q ∂νL0, Integrable f (κR q)) ∧
        Integrable (fun q => ∫ z, ‖f z‖ ∂κR q) νL0) ∧
      (Integrable f νM0 →
        AEStronglyMeasurable (radicalAverage F h μR f) νL0 ∧
        Integrable (radicalAverage F h μR f) νL0 ∧
        (∫ q, radicalAverage F h μR f q ∂νL0) =
          c.toReal • ∫ z, f z ∂νM0))

/-- The scaled measure tower gives the full Tonelli, absolute-integrability
and Bochner conclusions for the supplied rectangular Haar and zero outer slice. -/
theorem radicalIntegration
    (μR : Measure R) [μR.IsAddHaarMeasure]
    (νL : Measure (LowerMixedQuotient F h))
    (hνL : IsCompatible (lowerMixedSubgroup F h) (generalLinearHaar F t)
      (lowerMixedHaar F h) νL)
    (νM : Measure (MixedQuotient F h))
    (hνM : IsCompatible (mixedSubgroup F h) (generalLinearHaar F t)
      (mixedHaar F h) νM) :
    RadicalIntegrationStatement F h μR νL νM := by
  have hc := Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.integerCube_mass_pos_lt_top F
    (m 1 + 1) (m 0 + 1) μR
  have hcomp := (radicalTower F h μR νL hνL νM hνM).2 0
  refine ⟨radicalKernel F h μR, radicalKernel_isSFinite F h μR,
    radicalKernel_mk F h μR, hcomp, ?_, ?_⟩
  · intro f hf
    exact TwoBlockUnipotentQuotient.lintegral_lintegral_of_comp_eq_smul hcomp hf
  · intro f hf
    refine ⟨TwoBlockUnipotentQuotient.integrable_iff_of_comp_eq_smul
      hcomp hc.1.ne' hc.2.ne hf.aestronglyMeasurable, ?_⟩
    intro hfi
    rw [radicalAverage_eq_integral_radicalKernel F h μR f hf]
    obtain ⟨hi, he⟩ := TwoBlockUnipotentQuotient.integral_integral_of_comp_eq_smul
      hcomp hc.2.ne hfi
    exact ⟨hi.aestronglyMeasurable, hi, he⟩

end Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
