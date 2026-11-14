import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockMeasures
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockMeasures
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientData
/-!
# Haar measure in the actual lower mixed coordinates

The coordinate product measure is invariant on both sides, although its
coordinate homeomorphism is not a group homomorphism.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
open Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient hiding LowerMixedQuotient continuous_determinantOrder continuous_firstBlockFiberPoint continuous_projectionFromLower continuous_projectionFromMixed continuous_radicalFiberPoint determinantOrder determinantOrder_mk determinantOrder_projectionFromLower determinantOrder_projectionFromMixed determinantOrder_radicalFiberPoint determinantSlice firstBlockAverage firstBlockAverage_mk firstBlockEmbedding_mul_lowerRadical_mul_mixedEmbedding firstBlockFiberIntegral firstBlockFiberIntegral_def firstBlockFiberIntegral_lowerMixedSubgroup_mul firstBlockFiberIntegral_lowerRadical_mixedEmbedding_mul firstBlockFiberPoint firstBlockFiberPoint_lowerRadical_mixedEmbedding_mul firstBlockFiberPoint_mk integral_comp_radicalChange isClopen_determinantSlice isClosed_lowerMixedSubgroup lowerBlockUnipotent_le_lowerMixedSubgroup lowerMeasuresInstance01 lowerMeasuresInstance02 lowerMeasuresInstance03 lowerMeasuresInstance04 lowerMeasuresInstance05 lowerMeasuresInstance06 lowerMeasuresInstance07 lowerMeasuresInstance08 lowerMeasuresInstance09 lowerMeasuresInstance10 lowerMeasuresInstance13 lowerMeasuresInstance14 lowerMeasuresInstance15 lowerMeasuresInstance16 lowerMeasuresInstance17 lowerMeasuresInstance18 lowerMeasuresInstance19 lowerMeasuresInstance20 lowerMeasuresInstance21 lowerMeasuresInstance22 lowerMeasuresInstance23 lowerMeasuresInstance24 lowerMixedCoordinates lowerMixedCoordinates_lowerProduct lowerMixedDiagonal lowerMixedDiagonal_fst_val lowerMixedDiagonal_lowerProduct lowerMixedDiagonal_snd_val lowerMixedProductMeasure lowerMixedProductMeasure_isHaar lowerMixedProductMeasure_isMulLeftInvariant lowerMixedProductMeasure_isMulRightInvariant lowerMixedSubgroup lowerMixedSubgroupEquiv lowerMixedSubgroupEquiv_apply_val lowerMixedSubgroupEquiv_mul lowerMixedSubgroupEquiv_symm_apply_fst lowerMixedSubgroupHomeomorph lowerMixedSubgroup_le_normOneSubgroup lowerMixedSubgroup_le_oppositeParabolic lowerMixed_decomposition lowerProduct_lowerMixedCoordinates lowerProduct_mem lowerRadical_mul_leviEmbedding_one_mem measurableSet_determinantSlice measurePreserving_radicalChange mem_lowerMixedSubgroup_iff mixedSubgroup_le_lowerMixedSubgroup mk_mem_determinantSlice projectionFromLower projectionFromLower_mk projectionFromLower_preimage_determinantSlice projectionFromMixed projectionFromMixed_mk projectionFromMixed_preimage_determinantSlice radicalAverage radicalAverage_mk radicalChange radicalChangeHomeomorph radicalChangeHomeomorph_apply radicalChange_apply radicalFiberIntegral radicalFiberIntegral_def radicalFiberIntegral_lowerMixedSubgroup_mul radicalFiberIntegral_lowerRadical_mixedEmbedding_mul radicalFiberPoint radicalFiberPoint_def radicalFiberPoint_lowerRadical_mixedEmbedding_mul radicalFiberPoint_mem_determinantSlice_iff
open Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice

open _root_.MeasureTheory TopologicalSpace
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockFirstBlockQuotient hiding MixedQuotient NormOneRightInvariant blockUnipotent_le_mixedSubgroup continuous_determinantOrder continuous_fiberPoint determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice determinant_mixedEmbedding fiberIntegral fiberIntegral_def fiberIntegral_mixedEmbedding_mul fiberIntegral_mixedSubgroup_mul fiberPoint_mem_determinantSlice_iff fiberPoint_mixedEmbedding_mul firstBlockAverage firstBlockAverage_mk firstBlockAverage_rightTranslate instBorelSpaceGeneralLinearCarrier instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instIsNonarchimedeanLocalFieldCarrier instLocallyCompactSpaceMatrixFinCarrier instLocallyCompactSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instLocallyCompactSpaceSubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceGeneralLinearCarrier instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instSecondCountableTopologyGeneralLinearCarrier instSecondCountableTopologySubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instSecondCountableTopologySubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instT2SpaceCarrier instTopologicalSpaceCarrier instValuativeRelCarrier isClopen_determinantSlice isClosed_mixedSubgroup isOpenEmbedding_normOneSubtype map_normOneHaar measurableSet_determinantSlice mem_determinantSlice mem_mixedSubgroup_iff mem_mixedSubgroup_iff_determinantNorm mem_normOneSubgroup_iff mem_normOneSubgroup_iff_normalizedAbs mixedCoordinates mixedCoordinates_mixedEmbedding mixedEmbedding mixedEmbedding_apply mixedEmbedding_index_one_one mixedEmbedding_index_one_zero mixedEmbedding_index_zero_one mixedEmbedding_index_zero_zero mixedEmbedding_mem mixedEmbedding_mixedCoordinates mixedHaar mixedHaar_isHaar mixedHaar_isMulRightInvariant mixedHaar_regular mixedSubgroup mixedSubgroupEquiv mixedSubgroupEquiv_apply_val mixedSubgroupHomeomorph mixedSubgroup_le_normOneSubgroup mixedSubgroup_le_parabolic mixed_compatibleMeasureExists mk_mem_determinantSlice normOneHaar normOneHaar_isHaar normOneHaar_isMulRightInvariant normOneHaar_regular normOneRightInvariant_of_isCompatible normOneSubgroup ord_determinant_eq_zero rightTranslate_mem_determinantSlice
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice firstBlockAverage firstBlockAverage_mk isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open scoped ENNReal

universe uF

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance lowerMeasuresInstance04 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance lowerMeasuresInstance05 : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance lowerMeasuresInstance06 : MeasurableSpace F := borel _
local instance lowerMeasuresInstance07 : BorelSpace F := ⟨rfl⟩
local instance lowerMeasuresInstance08 (a b : ℕ) : LocallyCompactSpace (Matrix (Fin b) (Fin a) F) :=
  inferInstanceAs (LocallyCompactSpace (Fin b → Fin a → F))
local instance lowerMeasuresInstance09 (a b : ℕ) : SecondCountableTopology (Matrix (Fin b) (Fin a) F) :=
  inferInstanceAs (SecondCountableTopology (Fin b → Fin a → F))
local instance lowerMeasuresInstance10 (n : ℕ) : IsTopologicalGroup (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup n
local instance lowerMeasuresInstance13 (n : ℕ) : SecondCountableTopology (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology n
local instance lowerMeasuresInstance14 (n : ℕ) : LocallyCompactSpace (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace n
local instance lowerMeasuresInstance15 (n : ℕ) : MeasurableSpace (normOneSubgroup F n) := borel _
local instance lowerMeasuresInstance16 (n : ℕ) : BorelSpace (normOneSubgroup F n) := ⟨rfl⟩
local instance lowerMeasuresInstance17 (n : ℕ) : SecondCountableTopology (normOneSubgroup F n) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerMeasuresInstance18 (n : ℕ) : LocallyCompactSpace (normOneSubgroup F n) :=
  (isOpenEmbedding_normOneSubtype F n).locallyCompactSpace
local instance lowerMeasuresInstance19 (n : ℕ) : MeasurableSpace (upperUnipotent n F) := borel _
local instance lowerMeasuresInstance20 (n : ℕ) : BorelSpace (upperUnipotent n F) := ⟨rfl⟩
local instance lowerMeasuresInstance21 (n : ℕ) : SecondCountableTopology (upperUnipotent n F) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerMeasuresInstance22 (n : ℕ) : LocallyCompactSpace (upperUnipotent n F) :=
  UpperUnipotent.locallyCompactSpace
local instance lowerMeasuresInstance23 : MeasurableSpace (lowerMixedSubgroup F h) := borel _
local instance lowerMeasuresInstance24 : BorelSpace (lowerMixedSubgroup F h) := ⟨rfl⟩

local notation "R" => Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F
local notation "D" => normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F
local notation "μD" => Measure.prod (normOneHaar F (m 0)) (unipotentHaar F (m 1))

/-- Product of the supplied rectangular Haar and the fixed diagonal measures,
transported by the actual lower mixed coordinate homeomorphism. -/
def lowerMixedProductMeasure (μR : Measure R) : Measure (lowerMixedSubgroup F h) :=
  Measure.map (lowerMixedSubgroupHomeomorph F h) (μR.prod μD)

private theorem measurePreserving_coordinateLeft (μR : Measure R) [μR.IsAddHaarMeasure]
    (x : R × D) :
    MeasurePreserving
      (fun y : R × D =>
        (x.1 + x.2.2.val.val * y.1 * (x.2.1.val⁻¹).val, x.2 * y.2))
      (μR.prod μD) (μR.prod μD) := by
  have hc := measurePreserving_radicalChange F μR 0 x.2.1⁻¹ x.2.2⁻¹
  have hl : MeasurePreserving
      (fun Z : R => x.1 + x.2.2.val.val * Z * (x.2.1.val⁻¹).val) μR μR := by
    simpa only [Function.comp_def, radicalChange_apply, Subgroup.coe_inv, inv_inv,
      add_zero] using (measurePreserving_add_left μR x.1).comp hc
  exact hl.prod (measurePreserving_mul_left μD x.2)

private theorem measurePreserving_coordinateRight (μR : Measure R) [μR.IsAddHaarMeasure]
    (x : R × D) :
    MeasurePreserving
      (fun y : R × D =>
        (y.1 + y.2.2.val.val * x.1 * (y.2.1.val⁻¹).val, y.2 * x.2))
      (μR.prod μD) (μR.prod μD) := by
  have hc : Continuous (fun y : D × R =>
      y.2 + y.1.2.val.val * x.1 * (y.1.1.val⁻¹).val) := by
    exact continuous_snd.add
      (((Units.continuous_val.comp (continuous_subtype_val.comp
        (continuous_snd.comp continuous_fst))).matrix_mul continuous_const).matrix_mul
          (Units.continuous_val.comp (continuous_subtype_val.comp
            (continuous_fst.comp continuous_fst)).inv))
  have hp := (measurePreserving_mul_right μD x.2).skew_product hc.measurable
    (Filter.Eventually.of_forall (fun d : D => map_add_right_eq_self μR
      (d.2.val.val * x.1 * (d.1.val⁻¹).val)))
  exact (Measure.measurePreserving_swap (μ := μD) (ν := μR)).comp
    (hp.comp (Measure.measurePreserving_swap (μ := μR) (ν := μD)))

instance lowerMixedProductMeasure_isMulLeftInvariant
    (μR : Measure R) [μR.IsAddHaarMeasure] :
    (lowerMixedProductMeasure F h μR).IsMulLeftInvariant := by
  let e := lowerMixedSubgroupHomeomorph F h
  refine ⟨fun g => ?_⟩
  obtain ⟨x, rfl⟩ := e.surjective g
  change Measure.map (fun z => e x * z) (Measure.map e (μR.prod μD)) =
    Measure.map e (μR.prod μD)
  rw [Measure.map_map (measurable_const_mul (e x)) e.continuous.measurable]
  have he : (fun y => e x * e y) = e ∘
      (fun y : R × D =>
        (x.1 + x.2.2.val.val * y.1 * (x.2.1.val⁻¹).val, x.2 * y.2)) := by
    funext y
    exact lowerMixedSubgroupEquiv_mul F h x y
  change Measure.map (fun y => e x * e y) (μR.prod μD) = _
  rw [he, ← Measure.map_map e.continuous.measurable
    (measurePreserving_coordinateLeft F μR x).measurable,
    (measurePreserving_coordinateLeft F μR x).map_eq]

instance lowerMixedProductMeasure_isMulRightInvariant
    (μR : Measure R) [μR.IsAddHaarMeasure] :
    (lowerMixedProductMeasure F h μR).IsMulRightInvariant := by
  let e := lowerMixedSubgroupHomeomorph F h
  refine ⟨fun g => ?_⟩
  obtain ⟨x, rfl⟩ := e.surjective g
  change Measure.map (fun z => z * e x) (Measure.map e (μR.prod μD)) =
    Measure.map e (μR.prod μD)
  rw [Measure.map_map (measurable_mul_const (e x)) e.continuous.measurable]
  have he : (fun y => e y * e x) = e ∘
      (fun y : R × D =>
        (y.1 + y.2.2.val.val * x.1 * (y.2.1.val⁻¹).val, y.2 * x.2)) := by
    funext y
    exact lowerMixedSubgroupEquiv_mul F h y x
  change Measure.map (fun y => e y * e x) (μR.prod μD) = _
  rw [he, ← Measure.map_map e.continuous.measurable
    (measurePreserving_coordinateRight F μR x).measurable,
    (measurePreserving_coordinateRight F μR x).map_eq]

instance lowerMixedProductMeasure_isHaar
    (μR : Measure R) [μR.IsAddHaarMeasure] :
    (lowerMixedProductMeasure F h μR).IsHaarMeasure where
  toIsFiniteMeasureOnCompacts :=
    Measure.IsFiniteMeasureOnCompacts.map (μR.prod μD) (lowerMixedSubgroupHomeomorph F h)
  toIsOpenPosMeasure := (lowerMixedSubgroupHomeomorph F h).continuous.isOpenPosMeasure_map
    (lowerMixedSubgroupHomeomorph F h).surjective

end Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
