import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockFiberKernels
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockFiberKernel
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientData
/-!
# Actual lower mixed quotient fiber kernels

Measurable descent of the rectangular and small-slice pushforward measures.
These constructions supply neither a normalized measure tower nor convergence.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
open Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient hiding LowerMixedQuotient continuous_determinantOrder continuous_firstBlockFiberPoint continuous_projectionFromLower continuous_projectionFromMixed continuous_radicalFiberPoint determinantOrder determinantOrder_mk determinantOrder_projectionFromLower determinantOrder_projectionFromMixed determinantOrder_radicalFiberPoint determinantSlice firstBlockAverage firstBlockAverage_mk firstBlockEmbedding_mul_lowerRadical_mul_mixedEmbedding firstBlockFiberIntegral firstBlockFiberIntegral_def firstBlockFiberIntegral_lowerMixedSubgroup_mul firstBlockFiberIntegral_lowerRadical_mixedEmbedding_mul firstBlockFiberMeasures_lowerMixed_mul firstBlockFiberPoint firstBlockFiberPoint_lowerRadical_mixedEmbedding_mul firstBlockFiberPoint_mk firstBlockKernel firstBlockKernel_mk instBorelSpaceCarrier instBorelSpaceGeneralLinearCarrier instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceLowerMixedQuotient instBorelSpaceLowerQuotientCarrier instBorelSpaceMixedQuotient instIsNonarchimedeanLocalFieldCarrier instLocallyCompactSpaceGeneralLinearCarrier instLocallyCompactSpaceMatrixFinCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceLowerMixedQuotient instMeasurableSpaceLowerQuotientCarrier instMeasurableSpaceMixedQuotient instSecondCountableTopologyCarrier instSecondCountableTopologyGeneralLinearCarrier instSecondCountableTopologyMatrixFinCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instValuativeRelCarrier integral_comp_radicalChange isClopen_determinantSlice isClosed_lowerMixedSubgroup lowerBlockUnipotent_le_lowerMixedSubgroup lowerMixedCoordinates lowerMixedCoordinates_lowerProduct lowerMixedDiagonal lowerMixedDiagonal_fst_val lowerMixedDiagonal_lowerProduct lowerMixedDiagonal_snd_val lowerMixedSubgroup lowerMixedSubgroupEquiv lowerMixedSubgroupEquiv_apply_val lowerMixedSubgroupEquiv_mul lowerMixedSubgroupEquiv_symm_apply_fst lowerMixedSubgroupHomeomorph lowerMixedSubgroup_le_normOneSubgroup lowerMixedSubgroup_le_oppositeParabolic lowerMixed_decomposition lowerProduct_lowerMixedCoordinates lowerProduct_mem lowerRadical_mul_leviEmbedding_one_mem measurableSet_determinantSlice measurable_firstBlockFiberMeasures measurable_radicalFiberMeasures measurePreserving_radicalChange mem_lowerMixedSubgroup_iff mixedSubgroup_le_lowerMixedSubgroup mk_mem_determinantSlice projectionFromLower projectionFromLower_mk projectionFromLower_preimage_determinantSlice projectionFromMixed projectionFromMixed_mk projectionFromMixed_preimage_determinantSlice radicalAverage radicalAverage_mk radicalChange radicalChangeHomeomorph radicalChangeHomeomorph_apply radicalChange_apply radicalFiberIntegral radicalFiberIntegral_def radicalFiberIntegral_lowerMixedSubgroup_mul radicalFiberIntegral_lowerRadical_mixedEmbedding_mul radicalFiberMeasures_lowerMixed_mul radicalFiberPoint radicalFiberPoint_def radicalFiberPoint_lowerRadical_mixedEmbedding_mul radicalFiberPoint_mem_determinantSlice_iff radicalKernel radicalKernel_mk
open Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice

open _root_.MeasureTheory ProbabilityTheory
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockFirstBlockQuotient hiding MixedQuotient NormOneRightInvariant blockUnipotent_le_mixedSubgroup continuous_determinantOrder continuous_fiberPoint determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice determinant_mixedEmbedding fiberIntegral fiberIntegral_def fiberIntegral_mixedEmbedding_mul fiberIntegral_mixedSubgroup_mul fiberKernel fiberKernel_mk fiberMeasures_mixedSubgroup_mul fiberPoint_mem_determinantSlice_iff fiberPoint_mixedEmbedding_mul firstBlockAverage firstBlockAverage_mk firstBlockAverage_rightTranslate instBorelSpaceBlockQuotientCarrier instBorelSpaceGeneralLinearCarrier instBorelSpaceGeneralLinearCarrier_1 instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceMixedQuotient instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instLocallyCompactSpaceGeneralLinearCarrier instLocallyCompactSpaceMatrixFinCarrier instLocallyCompactSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instLocallyCompactSpaceSubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceBlockQuotientCarrier instMeasurableSpaceGeneralLinearCarrier instMeasurableSpaceGeneralLinearCarrier_1 instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceMixedQuotient instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instSecondCountableTopologyGeneralLinearCarrier instSecondCountableTopologyGeneralLinearCarrier_1 instSecondCountableTopologySubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instSecondCountableTopologySubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instT2SpaceCarrier instT2SpaceCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 isClopen_determinantSlice isClosed_mixedSubgroup isOpenEmbedding_normOneSubtype map_normOneHaar map_restrict_smallSlice measurableSet_determinantSlice measurable_fiberMeasures mem_determinantSlice mem_mixedSubgroup_iff mem_mixedSubgroup_iff_determinantNorm mem_normOneSubgroup_iff mem_normOneSubgroup_iff_normalizedAbs mixedCoordinates mixedCoordinates_mixedEmbedding mixedEmbedding mixedEmbedding_apply mixedEmbedding_index_one_one mixedEmbedding_index_one_zero mixedEmbedding_index_zero_one mixedEmbedding_index_zero_zero mixedEmbedding_mem mixedEmbedding_mixedCoordinates mixedHaar mixedHaar_isHaar mixedHaar_isMulRightInvariant mixedHaar_regular mixedSubgroup mixedSubgroupEquiv mixedSubgroupEquiv_apply_val mixedSubgroupHomeomorph mixedSubgroup_le_normOneSubgroup mixedSubgroup_le_parabolic mixed_compatibleMeasureExists mk_mem_determinantSlice normOneHaar normOneHaar_isHaar normOneHaar_isMulRightInvariant normOneHaar_regular normOneRightInvariant_of_isCompatible normOneSubgroup ord_determinant_eq_zero rightTranslate_mem_determinantSlice
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice firstBlockAverage firstBlockAverage_mk isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice

universe uF

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance : MeasurableSpace F := borel _
local instance : BorelSpace F := ⟨rfl⟩
local instance (a b : ℕ) :
    LocallyCompactSpace (Matrix (Fin b) (Fin a) F) :=
  inferInstanceAs (LocallyCompactSpace (Fin b → Fin a → F))
local instance (a b : ℕ) :
    SecondCountableTopology (Matrix (Fin b) (Fin a) F) :=
  inferInstanceAs (SecondCountableTopology (Fin b → Fin a → F))
local instance (n : ℕ) : MeasurableSpace (GeneralLinear n F) := borel _
local instance (n : ℕ) : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
local instance (n : ℕ) : SecondCountableTopology (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology n
local instance (n : ℕ) : LocallyCompactSpace (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace n
local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n F) := borel _
local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
local instance : MeasurableSpace (MixedQuotient F h) := borel _
local instance : BorelSpace (MixedQuotient F h) := ⟨rfl⟩
local instance : MeasurableSpace (LowerQuotient h F) := borel _
local instance : BorelSpace (LowerQuotient h F) := ⟨rfl⟩
local instance : MeasurableSpace (LowerMixedQuotient F h) := borel _
local instance : BorelSpace (LowerMixedQuotient F h) := ⟨rfl⟩

section Radical

variable (μR : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F))

/-- Joint continuity makes the unnormalized rectangular pushforwards measurable. -/
theorem measurable_radicalFiberMeasures [SFinite μR] :
    Measurable (fun g => Measure.map (fun Z => radicalFiberPoint F h Z g) μR) := by
  have hf := (continuous_radicalFiberPoint F h).measurable
  have hm := (Measure.measurable_map _ hf).comp (Measurable.map_prodMk_right (μ := μR))
  simpa only [Measure.map_map hf measurable_prodMk_right, Function.comp_def,
    Function.uncurry_apply_pair] using hm

/-- The supplied Haar measure is preserved by the actual change of representative. -/
theorem radicalFiberMeasures_lowerMixed_mul [μR.IsAddHaarMeasure]
    (l : lowerMixedSubgroup F h) (g : GeneralLinear (t + 1) F) :
    Measure.map (fun Z => radicalFiberPoint F h Z (l.val * g)) μR =
      Measure.map (fun Z => radicalFiberPoint F h Z g) μR := by
  obtain ⟨Z0, a0, n, hl⟩ := lowerMixed_decomposition F h l.property
  have hf : Measurable (fun Z => radicalFiberPoint F h Z g) :=
    ((continuous_radicalFiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
  rw [← hl]
  simp only [radicalFiberPoint_lowerRadical_mixedEmbedding_mul F h]
  change Measure.map ((fun Z => radicalFiberPoint F h Z g) ∘ radicalChange F Z0 a0 n) μR = _
  rw [← Measure.map_map hf (measurePreserving_radicalChange F μR Z0 a0 n).measurable,
    (measurePreserving_radicalChange F μR Z0 a0 n).map_eq]

/-- The actual rectangular kernel, with the supplied measure retained without rescaling. -/
def radicalKernel [μR.IsAddHaarMeasure] :
    Kernel (LowerMixedQuotient F h) (MixedQuotient F h) := by
  let κ := descend (lowerMixedSubgroup F h)
    (fun g => Measure.map (fun Z => radicalFiberPoint F h Z g) μR)
    (radicalFiberMeasures_lowerMixed_mul F h μR)
  exact ⟨κ, (measurable_quotient_iff _ (isClosed_lowerMixedSubgroup F h) κ).2
    (measurable_radicalFiberMeasures F h μR)⟩

/-- The rectangular representative law holds everywhere. -/
theorem radicalKernel_mk [μR.IsAddHaarMeasure] (g : GeneralLinear (t + 1) F) :
    radicalKernel F h μR (Quotient.mk _ g) =
      Measure.map (fun Z => radicalFiberPoint F h Z g) μR := rfl

end Radical

section FirstBlock

variable (νA : Measure (LeftUnipotentQuotient (m 0) F)) [SFinite νA]
  (hνA : NormOneRightInvariant F (m 0) νA)

/-- Joint continuity makes the small-slice pushforwards measurable. -/
theorem measurable_firstBlockFiberMeasures (k : ℤ) :
    Measurable (fun g => Measure.map (fun q => firstBlockFiberPoint F h q g)
      (νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k))) := by
  let := _root_.Topology.IsOpenQuotientMap.secondCountableTopology
    (leftQuotient_isOpenQuotientMap (upperUnipotent (m 0 + 1) F))
  let μ := νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k)
  have hf := (continuous_firstBlockFiberPoint F h).measurable
  have hm := (Measure.measurable_map _ hf).comp (Measurable.map_prodMk_right (μ := μ))
  simpa only [μ, Measure.map_map hf measurable_prodMk_right, Function.comp_def,
    Function.uncurry_apply_pair] using hm

omit [SFinite νA] in
include hνA in
/-- Norm-one right invariance on the small quotient gives lower mixed descent. -/
theorem firstBlockFiberMeasures_lowerMixed_mul (k : ℤ) (l : lowerMixedSubgroup F h)
    (g : GeneralLinear (t + 1) F) :
    Measure.map (fun q => firstBlockFiberPoint F h q (l.val * g))
        (νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k)) =
      Measure.map (fun q => firstBlockFiberPoint F h q g)
        (νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k)) := by
  obtain ⟨Z0, a0, n, hl⟩ := lowerMixed_decomposition F h l.property
  have hf : Measurable (fun q => firstBlockFiberPoint F h q g) :=
    ((continuous_firstBlockFiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
  rw [← hl]
  simp only [firstBlockFiberPoint_lowerRadical_mixedEmbedding_mul F h]
  change Measure.map ((fun q => firstBlockFiberPoint F h q g) ∘ rightTranslate _ a0.val) _ = _
  rw [← Measure.map_map hf (rightTranslate _ a0.val).measurable,
    Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.map_restrict_smallSlice F νA hνA k a0]

/-- The actual unweighted first-block slice kernel. -/
def firstBlockKernel (k : ℤ) :
    Kernel (LowerMixedQuotient F h) (LowerQuotient h F) := by
  let κ := descend (lowerMixedSubgroup F h)
    (fun g => Measure.map (fun q => firstBlockFiberPoint F h q g)
      (νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k)))
    (firstBlockFiberMeasures_lowerMixed_mul F h νA hνA k)
  exact ⟨κ, (measurable_quotient_iff _ (isClosed_lowerMixedSubgroup F h) κ).2
    (measurable_firstBlockFiberMeasures F h νA k)⟩

/-- The first-block representative law holds for every ambient representative. -/
theorem firstBlockKernel_mk (k : ℤ) (g : GeneralLinear (t + 1) F) :
    firstBlockKernel F h νA hνA k (Quotient.mk _ g) =
      Measure.map (fun q => firstBlockFiberPoint F h q g)
        (νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k)) := rfl

end FirstBlock

end Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
