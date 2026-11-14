import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockSliceTower
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockKernelShift
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockRadicalTower
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockUnipotentCoordinates
/-!
# The first-block slice tower of the lower mixed quotient

For every determinant order `k`, the unweighted first-block slice kernel composed with
the zero slice of a compatible lower mixed quotient measure is, after the density
`q^(-k b)`, the slice `k` of the compatible lower quotient measure.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
open Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient hiding LowerMixedQuotient RadicalTowerStatement ambientSlice continuous_determinantOrder continuous_firstBlockFiberPoint continuous_lowerMixedFirstQuotient continuous_projectionFromLower continuous_projectionFromMixed continuous_radicalFiberPoint continuous_rightRadicalCoord determinantOrder determinantOrder_mk determinantOrder_projectionFromLower determinantOrder_projectionFromMixed determinantOrder_radicalFiberPoint determinantSlice firstBlockAverage firstBlockAverage_mk firstBlockEmbedding_mul_lowerRadical_mul_mixedEmbedding firstBlockFiberIntegral firstBlockFiberIntegral_def firstBlockFiberIntegral_lowerMixedSubgroup_mul firstBlockFiberIntegral_lowerRadical_mixedEmbedding_mul firstBlockFiberMeasures_lowerMixed_mul firstBlockFiberPoint firstBlockFiberPoint_lowerRadical_mixedEmbedding_mul firstBlockFiberPoint_mk firstBlockFiberPoint_slice_isCompact_preimage firstBlockKernel firstBlockKernel_comp_zeroSlice firstBlockKernel_compact_ne_top firstBlockKernel_isSFinite firstBlockKernel_mk instBorelSpaceCarrier instBorelSpaceCarrier_1 instBorelSpaceGeneralLinearCarrier instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceLeftUnipotentQuotientCarrier_1 instBorelSpaceLowerMixedQuotient instBorelSpaceLowerQuotientCarrier instBorelSpaceLowerQuotientCarrier_1 instBorelSpaceMixedQuotient instBorelSpaceMixedQuotient_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instLocallyCompactSpaceGeneralLinearCarrier instLocallyCompactSpaceGeneralLinearCarrier_1 instLocallyCompactSpaceMatrixFinCarrier instMeasurableSpaceCarrier instMeasurableSpaceCarrier_1 instMeasurableSpaceGeneralLinearCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier_1 instMeasurableSpaceLowerMixedQuotient instMeasurableSpaceLowerQuotientCarrier instMeasurableSpaceLowerQuotientCarrier_1 instMeasurableSpaceMixedQuotient instMeasurableSpaceMixedQuotient_1 instSecondCountableTopologyCarrier instSecondCountableTopologyCarrier_1 instSecondCountableTopologyGeneralLinearCarrier instSecondCountableTopologyGeneralLinearCarrier_1 instSecondCountableTopologyMatrixFinCarrier instT2SpaceCarrier instT2SpaceCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 integral_comp_radicalChange isClopen_ambientSlice isClopen_determinantSlice isClosed_lowerMixedSubgroup lintegral_firstBlockFiberPoint_quotientAverageReal lintegral_firstBlockKernel_comp_quotientAverageReal lintegral_lowerHaar lintegral_lowerHaar_eq lintegral_mixedHaar_radical lintegral_mul_right_of_ord lintegral_radicalFiberPoint_quotientAverageReal lintegral_radicalKernel_comp_quotientAverageReal lintegral_unipotentHaar_blockCoordinates lowerBlockUnipotent_le_lowerMixedSubgroup lowerHaar lowerHaar_isHaar lowerHaar_isMulRightInvariant lowerHaar_regular lowerMeasureTransportInstance01 lowerMeasureTransportInstance02 lowerMeasureTransportInstance03 lowerMeasureTransportInstance04 lowerMeasureTransportInstance08 lowerMeasureTransportInstance09 lowerMeasureTransportInstance10 lowerMeasureTransportInstance11 lowerMeasureTransportInstance12 lowerMeasureTransportInstance13 lowerMeasureTransportInstance14 lowerMeasureTransportInstance17 lowerMeasureTransportInstance18 lowerMeasureTransportInstance21 lowerMeasureTransportInstance22 lowerMeasureTransportInstance23 lowerMeasureTransportInstance24 lowerMeasure_isCompatible lowerMeasure_sigmaFinite lowerMeasuresInstance01 lowerMeasuresInstance02 lowerMeasuresInstance03 lowerMeasuresInstance04 lowerMeasuresInstance05 lowerMeasuresInstance06 lowerMeasuresInstance07 lowerMeasuresInstance08 lowerMeasuresInstance09 lowerMeasuresInstance10 lowerMeasuresInstance13 lowerMeasuresInstance14 lowerMeasuresInstance15 lowerMeasuresInstance16 lowerMeasuresInstance17 lowerMeasuresInstance18 lowerMeasuresInstance19 lowerMeasuresInstance20 lowerMeasuresInstance21 lowerMeasuresInstance22 lowerMeasuresInstance23 lowerMeasuresInstance24 lowerMixedCoordinates lowerMixedCoordinates_lowerProduct lowerMixedDiagonal lowerMixedDiagonal_fst_val lowerMixedDiagonal_lowerProduct lowerMixedDiagonal_snd_val lowerMixedFirstQuotient lowerMixedFirstQuotient_lower_mul lowerMixedHaar lowerMixedHaar_integral lowerMixedHaar_isHaar lowerMixedHaar_isMulRightInvariant lowerMixedHaar_regular lowerMixedIntegralOpen lowerMixedIntegralOpen_isCompact lowerMixedProductMeasure lowerMixedProductMeasure_eq_smul lowerMixedProductMeasure_isHaar lowerMixedProductMeasure_isMulLeftInvariant lowerMixedProductMeasure_isMulRightInvariant lowerMixedSubgroup lowerMixedSubgroupEquiv lowerMixedSubgroupEquiv_apply_val lowerMixedSubgroupEquiv_mul lowerMixedSubgroupEquiv_symm_apply_fst lowerMixedSubgroupHomeomorph lowerMixedSubgroup_le_normOneSubgroup lowerMixedSubgroup_le_oppositeParabolic lowerMixed_compatibleMeasureExists lowerMixed_decomposition lowerMixed_preimage_integral lowerNormalizationInstance01 lowerNormalizationInstance02 lowerNormalizationInstance03 lowerNormalizationInstance04 lowerNormalizationInstance05 lowerNormalizationInstance06 lowerNormalizationInstance07 lowerNormalizationInstance08 lowerNormalizationInstance10 lowerNormalizationInstance11 lowerNormalizationInstance12 lowerNormalizationInstance13 lowerNormalizationInstance14 lowerNormalizationInstance15 lowerNormalizationInstance16 lowerNormalizationInstance17 lowerNormalizationInstance18 lowerNormalizationInstance19 lowerNormalizationInstance20 lowerNormalizationInstance21 lowerNormalizationInstance22 lowerNormalizationInstance23 lowerNormalizationInstance24 lowerNormalizationInstance25 lowerNormalizationInstance26 lowerProduct_lowerMixedCoordinates lowerProduct_mem lowerRadicalTowerInstance01 lowerRadicalTowerInstance02 lowerRadicalTowerInstance03 lowerRadicalTowerInstance04 lowerRadicalTowerInstance05 lowerRadicalTowerInstance06 lowerRadicalTowerInstance07 lowerRadicalTowerInstance08 lowerRadicalTowerInstance09 lowerRadicalTowerInstance10 lowerRadicalTowerInstance11 lowerRadicalTowerInstance12 lowerRadicalTowerInstance13 lowerRadicalTowerInstance14 lowerRadicalTowerInstance15 lowerRadicalTowerInstance16 lowerRadicalTowerInstance17 lowerRadicalTowerInstance18 lowerRadicalTowerInstance19 lowerRadicalTowerInstance20 lowerRadicalTowerInstance21 lowerRadicalTowerInstance22 lowerRadicalTowerInstance23 lowerRadicalTowerInstance24 lowerRadicalTowerInstance27 lowerRadicalTowerInstance28 lowerRadicalTowerInstance31 lowerRadicalTowerInstance32 lowerRadicalTowerInstance33 lowerRadicalTowerInstance34 lowerRadicalTowerInstance35 lowerRadicalTowerInstance36 lowerRadicalTowerInstance37 lowerRadical_mul_leviEmbedding_one_mem lowerSliceTowerInstance01 lowerSliceTowerInstance02 lowerSliceTowerInstance03 lowerSliceTowerInstance04 lowerSliceTowerInstance05 lowerSliceTowerInstance06 lowerSliceTowerInstance07 lowerSliceTowerInstance08 lowerSliceTowerInstance09 lowerSliceTowerInstance10 lowerSliceTowerInstance11 lowerSliceTowerInstance12 lowerSliceTowerInstance13 lowerSliceTowerInstance14 lowerSliceTowerInstance15 lowerSliceTowerInstance16 lowerSliceTowerInstance17 lowerSliceTowerInstance18 lowerSliceTowerInstance19 lowerSliceTowerInstance20 lowerSliceTowerInstance21 lowerSliceTowerInstance22 lowerSliceTowerInstance23 lowerSliceTowerInstance24 lowerSliceTowerInstance26 lowerSliceTowerInstance27 lowerSliceTowerInstance28 lowerSliceTowerInstance29 lowerSliceTowerInstance32 lowerSliceTowerInstance33 lowerSliceTowerInstance36 lowerSliceTowerInstance37 lowerSliceTowerInstance38 lowerSliceTowerInstance39 lowerSliceTowerInstance40 lowerSliceTowerInstance41 lowerSliceTowerInstance42 lowerUnipotentCoordinatesInstance01 lowerUnipotentCoordinatesInstance02 lowerUnipotentCoordinatesInstance03 lowerUnipotentCoordinatesInstance04 lowerUnipotentCoordinatesInstance05 lowerUnipotentCoordinatesInstance06 lowerUnipotentCoordinatesInstance07 lowerUnipotentCoordinatesInstance08 lowerUnipotentCoordinatesInstance09 lowerUnipotentCoordinatesInstance10 lowerUnipotentCoordinatesInstance11 lowerUnipotentCoordinatesInstance12 lowerUnipotentCoordinatesInstance13 lowerUnipotentCoordinatesInstance14 lowerUnipotentCoordinatesInstance15 lowerUnipotentCoordinatesInstance16 lowerUnipotentCoordinatesInstance17 lowerUnipotentCoordinatesInstance19 lowerUnipotentCoordinatesInstance20 lowerUnipotentCoordinatesInstance21 lowerUnipotentCoordinatesInstance22 lowerUnipotentCoordinatesInstance23 lowerUnipotentCoordinatesInstance24 measurableSet_determinantSlice measurable_firstBlockFiberMeasures measurable_radicalFiberMeasures measurePreserving_radicalChange mem_lowerMixedSubgroup_iff mixedSubgroup_le_lowerMixedSubgroup mk_mem_determinantSlice normOneHaar_integral ord_determinant_mul_of_mem projectionFromLower projectionFromLower_mk projectionFromLower_preimage_determinantSlice projectionFromMixed projectionFromMixed_mk projectionFromMixed_preimage_determinantSlice quotientAverageReal_indicator_ambientSlice quotientAverage_lower_transport radicalAverage radicalAverage_mk radicalChange radicalChangeHomeomorph radicalChangeHomeomorph_apply radicalChange_apply radicalFiberIntegral radicalFiberIntegral_def radicalFiberIntegral_lowerMixedSubgroup_mul radicalFiberIntegral_lowerRadical_mixedEmbedding_mul radicalFiberMeasures_lowerMixed_mul radicalFiberPoint radicalFiberPoint_def radicalFiberPoint_isCompact_preimage radicalFiberPoint_lowerRadical_mixedEmbedding_mul radicalFiberPoint_mem_determinantSlice_iff radicalKernel radicalKernel_comp radicalKernel_comp_restrict radicalKernel_compact_ne_top radicalKernel_isSFinite radicalKernel_mk radicalTower rightRadicalCoord rightRadicalCoord_mixed_mul_radical small_orbitKernel_comp_slice
open Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankLastRowReductionStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankLastRowReduction equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice

open _root_.MeasureTheory ProbabilityTheory
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockFirstBlockQuotient hiding MixedQuotient NormOneRightInvariant blockUnipotent_le_mixedSubgroup continuous_determinantOrder continuous_fiberPoint continuous_mixedFirstQuotient determinantOrder determinantOrder_mixedLeftShift determinantOrder_mk determinantOrder_rightTranslate determinantSlice determinant_mixedEmbedding exists_determinantOrder fiberIntegral fiberIntegral_def fiberIntegral_mixedEmbedding_mul fiberIntegral_mixedSubgroup_mul fiberKernel fiberKernel_comp_zeroSlice_eq fiberKernel_comp_zeroSlice_eq_zeroKernel_comp_slice fiberKernel_compact_ne_top fiberKernel_eq_zero_shift fiberKernel_isSFinite fiberKernel_mk fiberMeasures_mixedSubgroup_mul fiberPoint_firstBlockEmbedding_mul fiberPoint_mem_determinantSlice_iff fiberPoint_mixedEmbedding_mul fiberPoint_slice_isCompact_preimage firstBlockAverage firstBlockAverage_mk firstBlockAverage_rightTranslate firstBlockEmbedding_mem_mixedSubgroup instBorelSpaceBlockQuotientCarrier instBorelSpaceBlockQuotientCarrier_1 instBorelSpaceGeneralLinearCarrier instBorelSpaceGeneralLinearCarrier_1 instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceLeftUnipotentQuotientCarrier_1 instBorelSpaceMixedQuotient instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instLocallyCompactSpaceGeneralLinearCarrier instLocallyCompactSpaceGeneralLinearCarrier_1 instLocallyCompactSpaceMatrixFinCarrier instLocallyCompactSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instLocallyCompactSpaceSubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceBlockQuotientCarrier instMeasurableSpaceBlockQuotientCarrier_1 instMeasurableSpaceGeneralLinearCarrier instMeasurableSpaceGeneralLinearCarrier_1 instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier_1 instMeasurableSpaceMixedQuotient instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instSecondCountableTopologyGeneralLinearCarrier instSecondCountableTopologyGeneralLinearCarrier_1 instSecondCountableTopologyGeneralLinearCarrier_2 instSecondCountableTopologySubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instSecondCountableTopologySubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instT2SpaceCarrier instT2SpaceCarrier_1 instT2SpaceCarrier_2 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 isClopen_determinantSlice isClosed_mixedSubgroup isOpenEmbedding_normOneSubtype kernelShiftBlockQuotientBorel kernelShiftBlockQuotientMeasurable kernelShiftGLBorel kernelShiftGLMeasurable kernelShiftLocalField kernelShiftMixedBorel kernelShiftMixedMeasurable kernelShiftMixedQuotientBorel kernelShiftMixedQuotientMeasurable kernelShiftSmallQuotientBorel kernelShiftSmallQuotientMeasurable kernelShiftTopology kernelShiftUnipotentBorel kernelShiftUnipotentMeasurable kernelShiftValuativeRel lintegral_blockHaar map_mixedHaar_conjugation map_normOneHaar map_normOneHaar_conjugation map_restrict_mixedLeftShift map_restrict_smallSlice map_restrict_smallSlice_of_ord measurableSet_determinantSlice measurable_fiberMeasures measurePreserving_mixedLeftShift mem_determinantSlice mem_mixedSubgroup_iff mem_mixedSubgroup_iff_determinantNorm mem_normOneSubgroup_iff mem_normOneSubgroup_iff_normalizedAbs mixedCoordinates mixedCoordinates_mixedEmbedding mixedEmbedding mixedEmbedding_apply mixedEmbedding_index_one_one mixedEmbedding_index_one_zero mixedEmbedding_index_zero_one mixedEmbedding_index_zero_zero mixedEmbedding_mem mixedEmbedding_mixedCoordinates mixedFirstQuotient mixedFirstQuotient_block_mul mixedHaar mixedHaar_isHaar mixedHaar_isMulRightInvariant mixedHaar_regular mixedLeftShift mixedLeftShift_mk mixedSubgroup mixedSubgroupEquiv mixedSubgroupEquiv_apply_val mixedSubgroupHomeomorph mixedSubgroup_le_normOneSubgroup mixedSubgroup_le_parabolic mixed_compatibleMeasureExists mk_mem_determinantSlice mul_inv_mem_normOne_of_ord_eq normOneHaar normOneHaar_isHaar normOneHaar_isMulRightInvariant normOneHaar_regular normOneRightInvariant_of_isCompatible normOneSubgroup ord_determinant_eq_zero rightTranslate_mem_determinantSlice sliceShiftFieldT2 sliceShiftGLBorel sliceShiftGLLocallyCompact sliceShiftGLMeasurable sliceShiftGLSecondCountable sliceShiftLocalField sliceShiftMixedBorel sliceShiftMixedLocallyCompact sliceShiftMixedMeasurable sliceShiftMixedQuotientBorel sliceShiftMixedQuotientMeasurable sliceShiftNormOneBorel sliceShiftNormOneLocallyCompact sliceShiftNormOneMeasurable sliceShiftNormOneSecondCountable sliceShiftTopology sliceShiftUnipotentBorel sliceShiftUnipotentLocallyCompact sliceShiftUnipotentMeasurable sliceShiftUnipotentSecondCountable sliceShiftValuativeRel small_orbitKernel_comp_zero unfoldingInst1 unfoldingInst10 unfoldingInst11 unfoldingInst12 unfoldingInst13 unfoldingInst14 unfoldingInst15 unfoldingInst2 unfoldingInst20 unfoldingInst21 unfoldingInst23 unfoldingInst24 unfoldingInst3 unfoldingInst4 unfoldingInst8 unfoldingInst9
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice firstBlockAverage firstBlockAverage_mk isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open scoped ENNReal NNReal CompactlySupported ProbabilityTheory

universe uF

section Algebra


end Algebra

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance lowerSliceTowerInstance04 : T2Space F :=
  (⟨⟩ : LocalFieldData F).fieldT2
local instance lowerSliceTowerInstance05 : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance lowerSliceTowerInstance06 : MeasurableSpace F := borel _
local instance lowerSliceTowerInstance07 : BorelSpace F := ⟨rfl⟩
local instance lowerSliceTowerInstance08 (a b : ℕ) :
    LocallyCompactSpace (Matrix (Fin b) (Fin a) F) :=
  inferInstanceAs (LocallyCompactSpace (Fin b → Fin a → F))
local instance lowerSliceTowerInstance09 (a b : ℕ) :
    SecondCountableTopology (Matrix (Fin b) (Fin a) F) :=
  inferInstanceAs (SecondCountableTopology (Fin b → Fin a → F))
local instance lowerSliceTowerInstance10 (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup n
local instance lowerSliceTowerInstance11 (n : ℕ) :
    MeasurableSpace (GeneralLinear n F) := borel _
local instance lowerSliceTowerInstance12 (n : ℕ) :
    BorelSpace (GeneralLinear n F) := ⟨rfl⟩
local instance lowerSliceTowerInstance13 (n : ℕ) :
    SecondCountableTopology (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology n
local instance lowerSliceTowerInstance14 (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace n
local instance lowerSliceTowerInstance15 (n : ℕ) :
    MeasurableSpace (normOneSubgroup F n) := borel _
local instance lowerSliceTowerInstance16 (n : ℕ) : BorelSpace (normOneSubgroup F n) := ⟨rfl⟩
local instance lowerSliceTowerInstance17 (n : ℕ) :
    SecondCountableTopology (normOneSubgroup F n) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerSliceTowerInstance18 (n : ℕ) :
    LocallyCompactSpace (normOneSubgroup F n) :=
  (isOpenEmbedding_normOneSubtype F n).locallyCompactSpace
local instance lowerSliceTowerInstance19 (n : ℕ) :
    MeasurableSpace (upperUnipotent n F) := borel _
local instance lowerSliceTowerInstance20 (n : ℕ) :
    BorelSpace (upperUnipotent n F) := ⟨rfl⟩
local instance lowerSliceTowerInstance21 (n : ℕ) :
    SecondCountableTopology (upperUnipotent n F) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerSliceTowerInstance22 (n : ℕ) :
    LocallyCompactSpace (upperUnipotent n F) :=
  UpperUnipotent.locallyCompactSpace
local instance lowerSliceTowerInstance23 (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F) := borel _
local instance lowerSliceTowerInstance24 (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
local instance lowerSliceTowerInstance25 (n : ℕ) :
    SecondCountableTopology (LeftUnipotentQuotient n F) :=
  Topology.IsOpenQuotientMap.secondCountableTopology (leftQuotient_isOpenQuotientMap _)

section Slices

/-- The ambient determinant slice `G^k = {g | ord(det g) = k}` of `GL_n`. -/
def ambientSlice (n : ℕ) (k : ℤ) : Set (GeneralLinear n F) :=
  {g | (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant g : F) = k}

theorem isClopen_ambientSlice (n : ℕ) (k : ℤ) : IsClopen (ambientSlice F n k) :=
  (isClopen_discrete ({k} : Set ℤ)).preimage
    ((Langlands.AllField.RankinSelberg.continuous_ord_units (⟨⟩ : LocalFieldData F)).comp
      ((⟨⟩ : LocalFieldData F).generalLinearDeterminant n).continuous)

/-- Left multiplication by a norm-one matrix preserves the determinant order. -/
theorem ord_determinant_mul_of_mem {n : ℕ} {u : GeneralLinear n F}
    (hu : u ∈ normOneSubgroup F n) (g : GeneralLinear n F) :
    (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant (u * g) : F) =
      (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant g : F) := by
  rw [map_mul, Units.val_mul, (⟨⟩ : LocalFieldData F).ord_mul
    (GeneralLinear.determinant u).ne_zero (GeneralLinear.determinant g).ne_zero,
    ord_determinant_eq_zero F hu, zero_add]

/-- Averaging over a subgroup of `GL_n^0` commutes with cutting by an ambient slice. -/
theorem quotientAverageReal_indicator_ambientSlice {n : ℕ}
    (S : Subgroup (GeneralLinear n F)) (hS : S ≤ normOneSubgroup F n)
    [MeasurableSpace S] [MeasurableMul S] (μS : Measure S) [μS.IsMulRightInvariant]
    (f : GeneralLinear n F → ℝ) (k : ℤ) (g : GeneralLinear n F) :
    quotientAverageReal S μS ((ambientSlice F n k).indicator f) (Quotient.mk _ g) =
      (ambientSlice F n k).indicator
        (fun x => quotientAverageReal S μS f (Quotient.mk _ x)) g := by
  have hmem : ∀ s : S, s.val * g ∈ ambientSlice F n k ↔ g ∈ ambientSlice F n k := by
    intro s
    change (⟨⟩ : LocalFieldData F).ord _ = k ↔ (⟨⟩ : LocalFieldData F).ord _ = k
    rw [ord_determinant_mul_of_mem F (hS s.property)]
  rw [quotientAverageReal_mk]
  by_cases hg : g ∈ ambientSlice F n k
  · rw [Set.indicator_of_mem hg, quotientAverageReal_mk]
    exact integral_congr_ae (Filter.Eventually.of_forall fun s =>
      Set.indicator_of_mem ((hmem s).2 hg) f)
  · rw [Set.indicator_of_notMem hg]
    have hz : (fun s : S => (ambientSlice F n k).indicator f (s.val * g)) = fun _ => 0 :=
      funext fun s => Set.indicator_of_notMem (fun hs => hg ((hmem s).1 hs)) f
    rw [hz, integral_zero]

end Slices

section Scaling

variable {a b : ℕ}

/-- Right multiplication by `v` with `ord(det v) = k` scales every rectangular additive
Haar on `b × a` matrices by `q^(k b)`; the density `q^(-k b)` compensates it. -/
theorem lintegral_mul_right_of_ord
    (μR : Measure (Matrix (Fin b) (Fin a) F)) [μR.IsAddHaarMeasure]
    (φ : Matrix (Fin b) (Fin a) F → ℝ≥0∞) (hφ : Measurable φ)
    (v : GeneralLinear a F) (k : ℤ)
    (hv : (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant v : F) = k) :
    ENNReal.ofReal (((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^ (-(k * (b : ℤ)))) *
        ∫⁻ Z, φ (Z * v.val) ∂μR =
      ∫⁻ Z, φ Z ∂μR := by
  have hs := Langlands.AllField.HarmonicAnalysis.padicRectangularHaarScaling F (⟨⟩ : LocalFieldData F) b a μR
    1 v⁻¹
  simp only [inv_inv, Units.val_one, Matrix.one_mul] at hs
  have hm : Measurable (fun X : Matrix (Fin b) (Fin a) F => X * v.val) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hq : (0 : ℝ) < (⟨⟩ : LocalFieldData F).residueCardinality := by
    exact_mod_cast (zero_lt_one.trans (⟨⟩ : LocalFieldData F).residueCardinality_gt_one)
  have hc : (((((⟨⟩ : LocalFieldData F).determinantNorm b 1 : ℝ≥0) ^ a /
      ((⟨⟩ : LocalFieldData F).determinantNorm a v⁻¹ : ℝ≥0) ^ b)⁻¹ : ℝ≥0) : ℝ) =
      ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^ (k * (b : ℤ)) := by
    rw [map_one, map_inv, Units.val_one, Units.val_inv_eq_inv_val, one_pow, one_div, inv_inv,
      NNReal.coe_pow, NNReal.coe_inv,
      (⟨⟩ : LocalFieldData F).determinantNorm_eq_residue_pow a v, hv, zpow_neg, inv_inv,
      ← zpow_natCast, ← zpow_mul]
  rw [← lintegral_map hφ hm, hs, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul,
    ← mul_assoc, ← ENNReal.ofReal_coe_nnreal, hc,
    ← ENNReal.ofReal_mul (zpow_pos hq _).le, ← zpow_add₀ hq.ne', neg_add_cancel, zpow_zero,
    ENNReal.ofReal_one, one_mul]

end Scaling

section SmallOrbit

/-- The small orbital measure restricted to slice `k` is the left translate by `z` of the
norm-one Haar, for any `z` with `ord(det z) = k`. -/
theorem small_orbitKernel_comp_slice (n : ℕ)
    (νA : Measure (LeftUnipotentQuotient n F))
    (hνA : IsCompatible (upperUnipotent (n + 1) F)
      (generalLinearHaar F n) (unipotentHaar F n) νA)
    (z : GeneralLinear (n + 1) F) (k : ℤ)
    (hz : (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant z : F) = k) :
    orbitKernel (upperUnipotent (n + 1) F) (UpperUnipotent.isClosed (R := F))
        (unipotentHaar F n) ∘ₘ
      νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) n k) =
        Measure.map (fun u : normOneSubgroup F (n + 1) => z * u.val) (normOneHaar F n) := by
  let N := upperUnipotent (n + 1) F
  let κ := orbitKernel N (UpperUnipotent.isClosed (R := F)) (unipotentHaar F n)
  let s := Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) n k
  let π : GeneralLinear (n + 1) F → LeftUnipotentQuotient n F := Quotient.mk _
  have hs : MeasurableSet s := Langlands.AllField.RankinSelberg.isClosed_determinantSlice _ n k |>.measurableSet
  have hπ : Measurable π := continuous_quotient_mk'.measurable
  have hpt : ∀ A, MeasurableSet A → ∀ q,
      κ q (A ∩ π ⁻¹' s) = s.indicator (fun q => κ q A) q := by
    intro A hA q
    induction q using Quotient.inductionOn with
    | h g =>
      rw [show κ (Quotient.mk _ g) = _ from orbitKernel_mk N _ _ g,
        Measure.map_apply (continuous_subtype_val.mul_const g).measurable (hA.inter (hπ hs))]
      have he : ∀ a : N, π (a.val * g) = π g := fun a =>
        TwoBlockUnipotentQuotient.mk_mul_of_mem N a.property g
      by_cases hq : π g ∈ s
      · rw [Set.indicator_of_mem hq, show κ (Quotient.mk _ g) = _ from orbitKernel_mk N _ _ g,
          Measure.map_apply (continuous_subtype_val.mul_const g).measurable hA]
        congr 1
        ext a
        simp [he, hq]
      · rw [Set.indicator_of_notMem hq]
        have hempty : (fun a : N => a.val * g) ⁻¹' (A ∩ π ⁻¹' s) = ∅ := by
          ext a
          simp [he, hq]
        rw [hempty, measure_empty]
  have hcomp : κ ∘ₘ νA.restrict s = (generalLinearHaar F n).restrict (π ⁻¹' s) := by
    ext A hA
    rw [Measure.bind_apply hA κ.measurable.aemeasurable, Measure.restrict_apply hA,
      ← lintegral_indicator hs]
    rw [show (∫⁻ q, s.indicator (fun q => κ q A) q ∂νA) =
      ∫⁻ q, κ q (A ∩ π ⁻¹' s) ∂νA from
        lintegral_congr fun q => (hpt A hA q).symm]
    rw [← Measure.bind_apply (hA.inter (hπ hs)) κ.measurable.aemeasurable,
      show κ ∘ₘ νA = generalLinearHaar F n from
        orbitKernel_comp N (UpperUnipotent.isClosed (R := F)) _ _ νA hνA]
  let e := MeasurableEquiv.mulLeft z
  have hpre : e ⁻¹' (π ⁻¹' s) = (normOneSubgroup F (n + 1) : Set _) := by
    ext u
    change (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant (z * u) : F) = k ↔ _
    rw [map_mul, Units.val_mul, (⟨⟩ : LocalFieldData F).ord_mul
      (GeneralLinear.determinant z).ne_zero (GeneralLinear.determinant u).ne_zero, hz,
      add_eq_left, Langlands.LocalFieldData.ord_eq_zero_iff_normalizedAbs,
      Matrix.GeneralLinearGroup.val_det_apply, ← mem_normOneSubgroup_iff_normalizedAbs]
    rfl
  have hmap : Measure.map e (generalLinearHaar F n) = generalLinearHaar F n :=
    map_mul_left_eq_self (generalLinearHaar F n) z
  calc κ ∘ₘ νA.restrict s = (generalLinearHaar F n).restrict (π ⁻¹' s) := hcomp
    _ = (Measure.map e (generalLinearHaar F n)).restrict (π ⁻¹' s) := by rw [hmap]
    _ = Measure.map e ((generalLinearHaar F n).restrict (e ⁻¹' (π ⁻¹' s))) :=
      e.measurableEmbedding.restrict_map _ _
    _ = Measure.map e (Measure.map Subtype.val (normOneHaar F n)) := by
      rw [hpre, map_normOneHaar]
    _ = _ := Measure.map_map e.measurable continuous_subtype_val.measurable

end SmallOrbit

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance lowerSliceTowerInstance26 : MeasurableSpace (lowerBlockUnipotent h F) :=
  borel _
local instance lowerSliceTowerInstance27 : BorelSpace (lowerBlockUnipotent h F) := ⟨rfl⟩
local instance lowerSliceTowerInstance28 : MeasurableSpace (lowerMixedSubgroup F h) := borel _
local instance lowerSliceTowerInstance29 : BorelSpace (lowerMixedSubgroup F h) := ⟨rfl⟩
local instance lowerSliceTowerInstance30 : SecondCountableTopology (lowerMixedSubgroup F h) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerSliceTowerInstance31 : LocallyCompactSpace (lowerMixedSubgroup F h) :=
  (isClosed_lowerMixedSubgroup F h).locallyCompactSpace
local instance lowerSliceTowerInstance32 : MeasurableSpace (mixedSubgroup F h) := borel _
local instance lowerSliceTowerInstance33 : BorelSpace (mixedSubgroup F h) := ⟨rfl⟩
local instance lowerSliceTowerInstance34 : SecondCountableTopology (mixedSubgroup F h) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerSliceTowerInstance35 : LocallyCompactSpace (mixedSubgroup F h) :=
  (isClosed_mixedSubgroup F h).locallyCompactSpace
local instance lowerSliceTowerInstance36 : MeasurableSpace (LowerQuotient h F) := borel _
local instance lowerSliceTowerInstance37 : BorelSpace (LowerQuotient h F) := ⟨rfl⟩
local instance lowerSliceTowerInstance38 : T2Space (LowerQuotient h F) :=
  t2Space_lowerQuotient_canonical F h
local instance lowerSliceTowerInstance39 : LocallyCompactSpace (LowerQuotient h F) :=
  leftQuotient_locallyCompactSpace _
local instance lowerSliceTowerInstance40 : SecondCountableTopology (LowerQuotient h F) :=
  Topology.IsOpenQuotientMap.secondCountableTopology (leftQuotient_isOpenQuotientMap _)
local instance lowerSliceTowerInstance41 : MeasurableSpace (LowerMixedQuotient F h) := borel _
local instance lowerSliceTowerInstance42 : BorelSpace (LowerMixedQuotient F h) := ⟨rfl⟩

local notation "O" => Valuation.integer (ValuativeRel.valuation F)

section PerPoint

/-- **Per-point slice identity.** Over the small slice `k`, the density times the integral
of the `H⁻` averages at the first-block fiber points of `g` is the lower mixed average at
`g` of the left translate `x ↦ f(I(z) x)`, for any `z` with `ord(det z) = k`. -/
theorem lintegral_firstBlockFiberPoint_quotientAverageReal
    (νA : Measure (LeftUnipotentQuotient (m 0) F))
    (hνA : IsCompatible (upperUnipotent (m 0 + 1) F)
      (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) νA)
    (μR : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)) [μR.IsAddHaarMeasure]
    (f : C_c(GeneralLinear (t + 1) F, ℝ)) (hf0 : ∀ x, 0 ≤ f x)
    (k : ℤ) (z : GeneralLinear (m 0 + 1) F)
    (hz : (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant z : F) = k)
    (g : GeneralLinear (t + 1) F) :
    ENNReal.ofReal (((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
        (-(k * ((m 1 + 1 : ℕ) : ℤ)))) *
      ∫⁻ q, ENNReal.ofReal (quotientAverageReal (lowerBlockUnipotent h F)
          (lowerHaar F h) f (firstBlockFiberPoint F h q g))
        ∂νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k) =
      ENNReal.ofReal (quotientAverageReal (lowerMixedSubgroup F h) (lowerMixedHaar F h)
        (fun x => f (firstBlockEmbedding h F z * x)) (Quotient.mk _ g)) := by
  have hδT : ENNReal.ofReal (((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
      (-(k * ((m 1 + 1 : ℕ) : ℤ)))) ≠ ⊤ := ENNReal.ofReal_ne_top
  obtain ⟨hc0, hcT⟩ :=
    Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.integerCube_mass_pos_lt_top F (m 1 + 1) (m 0 + 1) μR
  have hR : Continuous (lowerRadical h F :
      Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F → GeneralLinear (t + 1) F) :=
    continuous_lowerRadical h F
  have hD : Continuous (fun x : GeneralLinear (m 0 + 1) F ×
      upperUnipotent (m 1 + 1) F =>
        (succBlockShape m h).leviEmbedding F (blockPair (m := m) F
          (x.1, x.2.val))) :=
    ((succBlockShape m h).leviEmbeddingContinuous F).continuous.comp
      ((continuous_blockPair F).comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  have hΨ : Measurable (fun p : (GeneralLinear (m 0 + 1) F ×
      upperUnipotent (m 1 + 1) F) × Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F =>
        ENNReal.ofReal (f ((succBlockShape m h).leviEmbedding F
          (blockPair (m := m) F (p.1.1, p.1.2.val)) * lowerRadical h F p.2 * g))) :=
    (ENNReal.continuous_ofReal.comp (f.continuous.comp
      (((hD.comp continuous_fst).mul (hR.comp continuous_snd)).mul continuous_const))).measurable
  have hG2 : Measurable (fun x : GeneralLinear (m 0 + 1) F ×
      upperUnipotent (m 1 + 1) F =>
        ∫⁻ Z, ENNReal.ofReal (f ((succBlockShape m h).leviEmbedding F
          (blockPair (m := m) F (x.1, x.2.val)) * lowerRadical h F Z * g))
          ∂μR) :=
    hΨ.lintegral_prod_right'
  let Φ : GeneralLinear (m 0 + 1) F → ℝ≥0∞ := fun u =>
    ∫⁻ y : upperUnipotent (m 1 + 1) F, ∫⁻ Z,
      ENNReal.ofReal (f ((succBlockShape m h).leviEmbedding F
        (blockPair (m := m) F (u, y.val)) * lowerRadical h F Z * g))
      ∂μR ∂unipotentHaar F (m 1)
  have hΦ : Measurable Φ := hG2.lintegral_prod_right'
  -- Step 1: the `H⁻` average at `[I(v) g]` in block coordinates, rescaled on slice `k`.
  have hpt : ∀ v : GeneralLinear (m 0 + 1) F,
      (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant v : F) = k →
      ENNReal.ofReal (((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
          (-(k * ((m 1 + 1 : ℕ) : ℤ)))) *
        (μR {Z | ∀ i j, Z i j ∈ O} *
          ENNReal.ofReal (quotientAverageReal (lowerBlockUnipotent h F) (lowerHaar F h) f
            (firstBlockFiberPoint F h (Quotient.mk _ v) g))) =
      ∫⁻ x : upperUnipotent (m 0 + 1) F, Φ (x.val * v)
        ∂unipotentHaar F (m 0) := by
    intro v hv
    have hψ : Measurable (fun x : GeneralLinear (t + 1) F =>
        ENNReal.ofReal (f (x * (firstBlockEmbedding h F v * g)))) :=
      (ENNReal.continuous_ofReal.comp
        (f.continuous.comp (continuous_id.mul continuous_const))).measurable
    have hav : ENNReal.ofReal (quotientAverageReal (lowerBlockUnipotent h F)
        (lowerHaar F h) f (firstBlockFiberPoint F h (Quotient.mk _ v) g)) =
        ∫⁻ x : lowerBlockUnipotent h F,
          ENNReal.ofReal (f (x.val * (firstBlockEmbedding h F v * g))) ∂lowerHaar F h := by
      rw [firstBlockFiberPoint_mk, quotientAverageReal_mk]
      exact ofReal_integral_eq_lintegral_ofReal
        (integrable_subgroup_mul _ (isClosed_lowerBlockUnipotent_canonical F h)
          (lowerHaar F h) f _)
        (Filter.Eventually.of_forall fun _ => hf0 _)
    have hinner : ∀ (y : upperUnipotent (m 1 + 1) F)
        (x : upperUnipotent (m 0 + 1) F),
        ENNReal.ofReal (((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
            (-(k * ((m 1 + 1 : ℕ) : ℤ)))) *
          ∫⁻ Z, ENNReal.ofReal (f ((succBlockShape m h).leviEmbedding F
            (blockPair (m := m) F (x.val, y.val)) * lowerRadical h F Z *
              (firstBlockEmbedding h F v * g))) ∂μR =
        ∫⁻ Z, ENNReal.ofReal (f ((succBlockShape m h).leviEmbedding F
          (blockPair (m := m) F (x.val * v, y.val)) * lowerRadical h F Z * g))
          ∂μR := by
      intro y x
      have hφ : Measurable (fun Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F =>
          ENNReal.ofReal (f ((succBlockShape m h).leviEmbedding F
            (blockPair (m := m) F (x.val * v, y.val)) * lowerRadical h F Z *
              g))) :=
        (ENNReal.continuous_ofReal.comp (f.continuous.comp
          ((continuous_const.mul hR).mul continuous_const))).measurable
      refine Eq.trans ?_ (lintegral_mul_right_of_ord F μR _ hφ v k hv)
      refine congrArg (HMul.hMul _) (lintegral_congr fun Z => ?_)
      rw [← mul_assoc, leviEmbedding_mul_lowerRadical_mul_firstBlockEmbedding]
    have hswap : AEMeasurable (Function.uncurry fun (y : upperUnipotent (m 1 + 1) F)
        (x : upperUnipotent (m 0 + 1) F) =>
          ∫⁻ Z, ENNReal.ofReal (f ((succBlockShape m h).leviEmbedding F
            (blockPair (m := m) F (x.val * v, y.val)) * lowerRadical h F Z * g))
            ∂μR)
        ((unipotentHaar F (m 1)).prod (unipotentHaar F (m 0))) :=
      (Measurable.lintegral_prod_right' (ν := μR)
        (f := fun p : (upperUnipotent (m 1 + 1) F × upperUnipotent (m 0 + 1) F) ×
          Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F =>
            ENNReal.ofReal (f ((succBlockShape m h).leviEmbedding F
              (blockPair (m := m) F (p.1.2.val * v, p.1.1.val)) *
                lowerRadical h F p.2 * g)))
        (ENNReal.continuous_ofReal.comp (f.continuous.comp
          (((((succBlockShape m h).leviEmbeddingContinuous F).continuous.comp
            ((continuous_blockPair F).comp
              (((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).mul
                continuous_const).prodMk
                (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))))).mul
            (hR.comp continuous_snd)).mul continuous_const))).measurable).aemeasurable
    rw [hav, lintegral_lowerHaar F h μR _ hψ, ← lintegral_const_mul' _ _ hδT]
    calc
      _ = ∫⁻ y : upperUnipotent (m 1 + 1) F, ∫⁻ x : upperUnipotent (m 0 + 1) F,
          ∫⁻ Z, ENNReal.ofReal (f ((succBlockShape m h).leviEmbedding F
            (blockPair (m := m) F (x.val * v, y.val)) * lowerRadical h F Z * g))
            ∂μR ∂unipotentHaar F (m 0) ∂unipotentHaar F (m 1) := by
        refine lintegral_congr fun y => ?_
        rw [← lintegral_const_mul' _ _ hδT]
        exact lintegral_congr fun x => hinner y x
      _ = _ := lintegral_lintegral_swap hswap
  -- Step 2: integrate over the small slice; the orbit kernel unfolds to `z GL^0`.
  let κA := orbitKernel (upperUnipotent (m 0 + 1) F)
    (UpperUnipotent.isClosed (R := F)) (unipotentHaar F (m 0))
  have hslice : MeasurableSet (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k) :=
    Langlands.AllField.RankinSelberg.isClosed_determinantSlice _ (m 0) k |>.measurableSet
  have hAQ : ENNReal.ofReal (((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
        (-(k * ((m 1 + 1 : ℕ) : ℤ)))) *
      (μR {Z | ∀ i j, Z i j ∈ O} *
        ∫⁻ q, ENNReal.ofReal (quotientAverageReal (lowerBlockUnipotent h F)
            (lowerHaar F h) f (firstBlockFiberPoint F h q g))
          ∂νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k)) =
      ∫⁻ u, Φ u ∂(κA ∘ₘ
        νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k)) := by
    rw [Measure.lintegral_bind κA.measurable.aemeasurable hΦ.aemeasurable,
      ← lintegral_const_mul' _ _ hcT.ne, ← lintegral_const_mul' _ _ hδT]
    refine setLIntegral_congr_fun hslice fun q hq => ?_
    revert hq
    induction q using Quotient.inductionOn with
    | h v =>
      intro hv
      rw [show κA (Quotient.mk _ v) = _ from orbitKernel_mk _ _ _ v,
        lintegral_map hΦ (continuous_subtype_val.mul_const v).measurable]
      exact hpt v hv
  -- Step 3: the norm-one integral of `Φ(z ·)` is the cube times the lower mixed average.
  have hψz : Measurable (fun x : GeneralLinear (t + 1) F =>
      ENNReal.ofReal (f (firstBlockEmbedding h F z * (x * g)))) :=
    (ENNReal.continuous_ofReal.comp (f.continuous.comp
      (continuous_const.mul (continuous_id.mul continuous_const)))).measurable
  have hm : Measurable (mixedSubgroupEquiv F h) :=
    (mixedSubgroupHomeomorph F h).continuous.measurable
  have hDm : Continuous (fun d : normOneSubgroup F (m 0 + 1) ×
      upperUnipotent (m 1 + 1) F => mixedEmbedding F h d) :=
    continuous_subtype_val.comp (mixedSubgroupHomeomorph F h).continuous
  have hprod : Measurable (fun p : (normOneSubgroup F (m 0 + 1) ×
      upperUnipotent (m 1 + 1) F) × Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F =>
        ENNReal.ofReal (f (firstBlockEmbedding h F z *
          (mixedEmbedding F h p.1 * lowerRadical h F p.2 * g)))) :=
    hψz.comp ((hDm.comp continuous_fst).mul (hR.comp continuous_snd)).measurable
  have hmix : ∫⁻ a0 : normOneSubgroup F (m 0 + 1), Φ (z * a0.val) ∂normOneHaar F (m 0) =
      μR {Z | ∀ i j, Z i j ∈ O} *
        ∫⁻ l : lowerMixedSubgroup F h,
          ENNReal.ofReal (f (firstBlockEmbedding h F z * (l.val * g)))
          ∂lowerMixedHaar F h := by
    calc
      _ = ∫⁻ a0 : normOneSubgroup F (m 0 + 1), ∫⁻ y : upperUnipotent (m 1 + 1) F,
            ∫⁻ Z, ENNReal.ofReal (f (firstBlockEmbedding h F z *
              (mixedEmbedding F h (a0, y) * lowerRadical h F Z * g)))
            ∂μR ∂unipotentHaar F (m 1) ∂normOneHaar F (m 0) := by
          refine lintegral_congr fun a0 => lintegral_congr fun y => lintegral_congr fun Z => ?_
          show ENNReal.ofReal (f ((succBlockShape m h).leviEmbedding F
              (blockPair (m := m) F (z * a0.val, y.val)) * lowerRadical h F Z *
                g)) = _
          rw [mixedEmbedding_apply, ← mul_assoc, ← mul_assoc,
            firstBlockEmbedding_mul_leviEmbedding]
      _ = ∫⁻ d, ∫⁻ Z, ENNReal.ofReal (f (firstBlockEmbedding h F z *
              (mixedEmbedding F h d * lowerRadical h F Z * g))) ∂μR
            ∂(normOneHaar F (m 0)).prod (unipotentHaar F (m 1)) :=
          (lintegral_prod _ hprod.lintegral_prod_right'.aemeasurable).symm
      _ = ∫⁻ Z, ∫⁻ d, ENNReal.ofReal (f (firstBlockEmbedding h F z *
              (mixedEmbedding F h d * lowerRadical h F Z * g)))
            ∂(normOneHaar F (m 0)).prod (unipotentHaar F (m 1)) ∂μR :=
          lintegral_lintegral_swap hprod.aemeasurable
      _ = ∫⁻ Z, ∫⁻ a : mixedSubgroup F h, ENNReal.ofReal (f (firstBlockEmbedding h F z *
              (a.val * lowerRadical h F Z * g))) ∂mixedHaar F h ∂μR := by
          refine lintegral_congr fun Z => ?_
          rw [mixedHaar, lintegral_map (f := fun a : mixedSubgroup F h =>
              ENNReal.ofReal (f (firstBlockEmbedding h F z *
                (a.val * lowerRadical h F Z * g))))
            (hψz.comp (continuous_subtype_val.mul_const _).measurable) hm]
          rfl
      _ = _ := lintegral_mixedHaar_radical F h μR _ hψz
  have hLavg : ENNReal.ofReal (quotientAverageReal (lowerMixedSubgroup F h) (lowerMixedHaar F h)
      (fun x => f (firstBlockEmbedding h F z * x)) (Quotient.mk _ g)) =
      ∫⁻ l : lowerMixedSubgroup F h,
        ENNReal.ofReal (f (firstBlockEmbedding h F z * (l.val * g)))
        ∂lowerMixedHaar F h := by
    rw [quotientAverageReal_mk]
    exact ofReal_integral_eq_lintegral_ofReal
      (integrable_subgroup_mul_of_hasCompactSupport (lowerMixedSubgroup F h)
        (isClosed_lowerMixedSubgroup F h) (lowerMixedHaar F h) _
        (f.continuous.comp (continuous_const.mul continuous_id))
        (f.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft _)) g)
      (Filter.Eventually.of_forall fun _ => hf0 _)
  have key : μR {Z | ∀ i j, Z i j ∈ O} *
      (ENNReal.ofReal (((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
          (-(k * ((m 1 + 1 : ℕ) : ℤ)))) *
        ∫⁻ q, ENNReal.ofReal (quotientAverageReal (lowerBlockUnipotent h F)
            (lowerHaar F h) f (firstBlockFiberPoint F h q g))
          ∂νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k)) =
      μR {Z | ∀ i j, Z i j ∈ O} *
        ENNReal.ofReal (quotientAverageReal (lowerMixedSubgroup F h) (lowerMixedHaar F h)
          (fun x => f (firstBlockEmbedding h F z * x)) (Quotient.mk _ g)) := by
    rw [mul_left_comm, hAQ, small_orbitKernel_comp_slice F (m 0) νA hνA z k hz,
      lintegral_map hΦ (show Measurable (fun u : normOneSubgroup F (m 0 + 1) => z * u.val) from
        (continuous_const.mul continuous_subtype_val).measurable), hmix, hLavg]
  exact (ENNReal.mul_right_inj hc0.ne' hcT.ne).mp key

/-- The composite first-block slice kernel integrates `H⁻` averages to the lower mixed
averages of the left translate `x ↦ f(I(z) x)`, after the density, for every outer measure. -/
theorem lintegral_firstBlockKernel_comp_quotientAverageReal
    (νA : Measure (LeftUnipotentQuotient (m 0) F)) [SFinite νA]
    (hInv : NormOneRightInvariant F (m 0) νA)
    (hνA : IsCompatible (upperUnipotent (m 0 + 1) F)
      (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) νA)
    (ν : Measure (LowerMixedQuotient F h))
    (f : C_c(GeneralLinear (t + 1) F, ℝ)) (hf0 : ∀ x, 0 ≤ f x)
    (k : ℤ) (z : GeneralLinear (m 0 + 1) F)
    (hz : (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant z : F) = k) :
    ENNReal.ofReal (((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
        (-(k * ((m 1 + 1 : ℕ) : ℤ)))) *
      ∫⁻ x, ENNReal.ofReal (quotientAverageReal (lowerBlockUnipotent h F)
          (lowerHaar F h) f x) ∂(firstBlockKernel F h νA hInv k ∘ₘ ν) =
      ∫⁻ q, ENNReal.ofReal (quotientAverageReal (lowerMixedSubgroup F h) (lowerMixedHaar F h)
        (fun x => f (firstBlockEmbedding h F z * x)) q) ∂ν := by
  have hHm : Measurable (fun x => ENNReal.ofReal (quotientAverageReal
      (lowerBlockUnipotent h F) (lowerHaar F h) f x)) :=
    (ENNReal.continuous_ofReal.comp (continuous_quotientAverageReal _
      (isClosed_lowerBlockUnipotent_canonical F h) _ f)).measurable
  rw [Measure.lintegral_bind (firstBlockKernel F h νA hInv k).measurable.aemeasurable
    hHm.aemeasurable, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun q => ?_
  induction q using Quotient.inductionOn with
  | h g =>
    have hfm : Measurable (fun a => firstBlockFiberPoint F h a g) :=
      ((continuous_firstBlockFiberPoint F h).comp
        (continuous_id.prodMk continuous_const)).measurable
    rw [firstBlockKernel_mk, lintegral_map hHm hfm]
    exact lintegral_firstBlockFiberPoint_quotientAverageReal F h νA hνA
      (Measure.addHaar : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F))
      f hf0 k z hz g

end PerPoint

section Extension

/-- Two measures on `H⁻ \ G` that integrate every nonnegative `H⁻` average to the same
finite value coincide. -/
theorem eq_of_lintegral_lowerQuotientAverageReal
    (μ₁ μ₂ : Measure (LowerQuotient h F))
    (I : C_c(GeneralLinear (t + 1) F, ℝ) → ℝ≥0∞)
    (hI : ∀ f : C_c(GeneralLinear (t + 1) F, ℝ), (∀ x, 0 ≤ f x) → I f < ⊤)
    (h₁ : ∀ f : C_c(GeneralLinear (t + 1) F, ℝ), (∀ x, 0 ≤ f x) →
      ∫⁻ q, ENNReal.ofReal (quotientAverageReal (lowerBlockUnipotent h F)
        (lowerHaar F h) f q) ∂μ₁ = I f)
    (h₂ : ∀ f : C_c(GeneralLinear (t + 1) F, ℝ), (∀ x, 0 ≤ f x) →
      ∫⁻ q, ENNReal.ofReal (quotientAverageReal (lowerBlockUnipotent h F)
        (lowerHaar F h) f q) ∂μ₂ = I f) :
    μ₁ = μ₂ := by
  let H := lowerBlockUnipotent h F
  let μH := lowerHaar F h
  have hH := isClosed_lowerBlockUnipotent_canonical F h
  have hlift : ∀ φ : C_c(LowerQuotient h F, ℝ), (∀ q, 0 ≤ φ q) →
      ∃ f : C_c(GeneralLinear (t + 1) F, ℝ), (∀ y, 0 ≤ f y) ∧
        ∀ q, quotientAverageReal H μH f q = φ q := by
    intro φ hφ
    obtain ⟨f, hf, hf0⟩ := realQuotientPositiveLifting H hH μH φ
    refine ⟨f, hf0 hφ, fun q => ?_⟩
    induction q using Quotient.inductionOn with
    | h g => exact hf g
  have hfin : ∀ μ' : Measure (LowerQuotient h F),
      (∀ f : C_c(GeneralLinear (t + 1) F, ℝ), (∀ x, 0 ≤ f x) →
        ∫⁻ q, ENNReal.ofReal (quotientAverageReal H μH f q) ∂μ' = I f) →
      IsFiniteMeasureOnCompacts μ' := by
    intro μ' hμ'
    refine ⟨fun C hC => ?_⟩
    obtain ⟨u, hu1, -, hucs, hu01⟩ :=
      exists_continuous_one_zero_of_isCompact hC isClosed_empty (Set.disjoint_empty C)
    let φ : C_c(LowerQuotient h F, ℝ) := ⟨u, hucs⟩
    obtain ⟨f, hf0, hfavg⟩ := hlift φ fun q => (hu01 q).1
    calc μ' C = ∫⁻ q, C.indicator 1 q ∂μ' :=
          (lintegral_indicator_one hC.isClosed.measurableSet).symm
      _ ≤ ∫⁻ q, ENNReal.ofReal (quotientAverageReal H μH f q) ∂μ' := by
          apply lintegral_mono
          intro q
          dsimp only
          rw [hfavg q]
          by_cases hq : q ∈ C
          · rw [Set.indicator_of_mem hq]
            change (1 : ENNReal) ≤ ENNReal.ofReal (u q)
            rw [hu1 hq, Pi.one_apply, ENNReal.ofReal_one]
          · rw [Set.indicator_of_notMem hq]
            exact zero_le
      _ = I f := hμ' f hf0
      _ < ⊤ := hI f hf0
  have : IsFiniteMeasureOnCompacts μ₁ := hfin μ₁ h₁
  have : IsFiniteMeasureOnCompacts μ₂ := hfin μ₂ h₂
  have : μ₁.Regular := inferInstance
  have : μ₂.Regular := inferInstance
  apply Measure.ext_of_integral_eq_on_compactlySupported_nnreal
  intro φ
  let φr : C_c(LowerQuotient h F, ℝ) :=
    ⟨⟨fun q => (φ q : ℝ), NNReal.continuous_coe.comp φ.continuous⟩,
      φ.hasCompactSupport.comp_left NNReal.coe_zero⟩
  obtain ⟨f, hf0, hfavg⟩ := hlift φr fun q => (φ q).coe_nonneg
  have key : ∀ μ' : Measure (LowerQuotient h F),
      ∫⁻ q, ENNReal.ofReal (quotientAverageReal H μH f q) ∂μ' = I f →
      ∫ q, (φ q : ℝ) ∂μ' = (I f).toReal := by
    intro μ' h'
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun q => (φ q).coe_nonneg)
      (NNReal.continuous_coe.comp φ.continuous).aestronglyMeasurable, ← h']
    congr 1
    apply lintegral_congr
    intro q
    rw [hfavg q]
    rfl
  rw [key _ (h₁ f hf0), key _ (h₂ f hf0)]

end Extension

section Tower

/-- **First-block slice tower.** For compatible measures and every determinant order `k`,
the density `q^(-k b)` times the first-block slice-`k` kernel composed with the zero slice
of the lower mixed quotient measure is the slice `k` of the lower quotient measure. -/
theorem firstBlockKernel_comp_zeroSlice
    (νA : Measure (LeftUnipotentQuotient (m 0) F)) [SFinite νA]
    (hInv : NormOneRightInvariant F (m 0) νA)
    (hνA : IsCompatible (upperUnipotent (m 0 + 1) F)
      (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) νA)
    (νL : Measure (LowerMixedQuotient F h))
    (hνL : IsCompatible (lowerMixedSubgroup F h) (generalLinearHaar F t)
      (lowerMixedHaar F h) νL)
    (νMinus : Measure (LowerQuotient h F))
    (hνMinus : IsCompatible (lowerBlockUnipotent h F) (generalLinearHaar F t)
      (lowerHaar F h) νMinus)
    (k : ℤ) :
    ENNReal.ofReal (((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
        (-(k * ((m 1 + 1 : ℕ) : ℤ)))) •
      (firstBlockKernel F h νA hInv k ∘ₘ
        νL.restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.determinantSlice F h 0)) =
      νMinus.restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k) := by
  obtain ⟨z, hz⟩ := Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.exists_determinantOrder F (m 0) k
  refine eq_of_lintegral_lowerQuotientAverageReal F h _ _
    (fun f => ∫⁻ x, ENNReal.ofReal ((ambientSlice F (t + 1) k).indicator f x)
      ∂generalLinearHaar F t)
    (fun f hf0 => ?_) (fun f hf0 => ?_) (fun f hf0 => ?_)
  · -- Finiteness of the common value.
    calc _ ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂generalLinearHaar F t :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal
            (Set.indicator_le_self' (fun x _ => hf0 x) x)
      _ < ⊤ := (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport).lintegral_lt_top
  · -- The tower side: unfold, cut by `G^0`, apply compatibility of `νL`, translate by `I(z)`.
    have hfzc : Continuous (fun x => f (firstBlockEmbedding h F z * x)) :=
      f.continuous.comp (continuous_const.mul continuous_id)
    have hfzs : HasCompactSupport (fun x => f (firstBlockEmbedding h F z * x)) :=
      f.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft _)
    have hpt : ∀ q : LowerMixedQuotient F h,
        (Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.determinantSlice F h 0).indicator
          (fun q => ENNReal.ofReal (quotientAverageReal (lowerMixedSubgroup F h)
            (lowerMixedHaar F h) (fun x => f (firstBlockEmbedding h F z * x)) q)) q =
        ENNReal.ofReal (quotientAverageReal (lowerMixedSubgroup F h) (lowerMixedHaar F h)
          ((ambientSlice F (t + 1) 0).indicator
            (fun x => f (firstBlockEmbedding h F z * x))) q) := by
      intro q
      induction q using Quotient.inductionOn with
      | h g =>
        rw [quotientAverageReal_indicator_ambientSlice F (lowerMixedSubgroup F h)
          (lowerMixedSubgroup_le_normOneSubgroup F h)]
        by_cases hg : g ∈ ambientSlice F (t + 1) 0
        · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (show (Quotient.mk _ g :
            LowerMixedQuotient F h) ∈ Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.determinantSlice F h 0
              from hg)]
        · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (show (Quotient.mk _ g :
            LowerMixedQuotient F h) ∉ Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.determinantSlice F h 0
              from hg), ENNReal.ofReal_zero]
    have hshift : ∀ x, (ambientSlice F (t + 1) 0).indicator
        (fun x => f (firstBlockEmbedding h F z * x)) x =
        (ambientSlice F (t + 1) k).indicator f (firstBlockEmbedding h F z * x) := by
      intro x
      have hmem : firstBlockEmbedding h F z * x ∈ ambientSlice F (t + 1) k ↔
          x ∈ ambientSlice F (t + 1) 0 := by
        change (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant
            (firstBlockEmbedding h F z * x) : F) = k ↔
          (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant x : F) = 0
        rw [map_mul, Units.val_mul, (⟨⟩ : LocalFieldData F).ord_mul
          (GeneralLinear.determinant (firstBlockEmbedding h F z)).ne_zero
          (GeneralLinear.determinant x).ne_zero, determinant_firstBlockEmbedding, hz,
          add_eq_left]
      by_cases hx : x ∈ ambientSlice F (t + 1) 0
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.2 hx)]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx (hmem.1 h'))]
    rw [lintegral_smul_measure, smul_eq_mul,
      lintegral_firstBlockKernel_comp_quotientAverageReal F h νA hInv hνA _ f hf0 k z hz,
      ← lintegral_indicator (Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.measurableSet_determinantSlice F h 0)]
    refine (lintegral_congr hpt).trans ?_
    rw [RecursiveIntegration.lintegral_quotientAverageReal _ _ _ νL hνL _
      ((isClopen_ambientSlice F (t + 1) 0).continuous_indicator hfzc)
      (hfzs.mono fun x hx h0 => hx (Set.indicator_apply_eq_zero.mpr fun _ => h0))
      (fun x => Set.indicator_nonneg (fun y _ => hf0 _) x)]
    refine (lintegral_congr fun x => by rw [hshift x]).trans ?_
    exact lintegral_mul_left_eq_self
      (fun x => ENNReal.ofReal ((ambientSlice F (t + 1) k).indicator f x))
      (firstBlockEmbedding h F z)
  · -- The lower quotient side: cut by `G^k` and apply compatibility of `νMinus`.
    have hpt : ∀ q : LowerQuotient h F,
        (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k).indicator
          (fun q => ENNReal.ofReal (quotientAverageReal (lowerBlockUnipotent h F)
            (lowerHaar F h) f q)) q =
        ENNReal.ofReal (quotientAverageReal (lowerBlockUnipotent h F) (lowerHaar F h)
          ((ambientSlice F (t + 1) k).indicator f) q) := by
      intro q
      induction q using Quotient.inductionOn with
      | h g =>
        rw [quotientAverageReal_indicator_ambientSlice F (lowerBlockUnipotent h F)
          ((lowerBlockUnipotent_le_lowerMixedSubgroup F h).trans
            (lowerMixedSubgroup_le_normOneSubgroup F h))]
        have hmem : (Quotient.mk _ g : LowerQuotient h F) ∈
            Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k ↔
              g ∈ ambientSlice F (t + 1) k :=
          Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.mk_mem_determinantSlice F h
        by_cases hg : g ∈ ambientSlice F (t + 1) k
        · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hmem.2 hg)]
        · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h' => hg (hmem.1 h')),
            ENNReal.ofReal_zero]
    rw [← lintegral_indicator (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.measurableSet_determinantSlice F h k)]
    refine (lintegral_congr hpt).trans ?_
    exact RecursiveIntegration.lintegral_quotientAverageReal _ _ _ νMinus hνMinus _
      ((isClopen_ambientSlice F (t + 1) k).continuous_indicator f.continuous)
      (f.hasCompactSupport.mono fun x hx h0 =>
        hx (Set.indicator_apply_eq_zero.mpr fun _ => h0))
      (fun x => Set.indicator_nonneg (fun y _ => hf0 y) x)

end Tower

end Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
