import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockQuotientIntegrationProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockFiberProper
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockKernelShift
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockQuotientAnalysis
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockQuotientTower
/-!
# Normalized first-block quotient integration
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankLastRowReductionStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt TwoBlockFirstBlockQuotientIntegrationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankLastRowReduction equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockFirstBlockQuotientIntegration zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory ProbabilityTheory
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockFirstBlockQuotient hiding FirstBlockKernelAnalysisStatement MixedQuotient NormOneRightInvariant NormalizedTowerStatement analytic_of_comp_eq blockUnipotent_le_mixedSubgroup continuous_determinantOrder continuous_fiberPoint continuous_mixedFirstQuotient determinantOrder determinantOrder_mixedLeftShift determinantOrder_mk determinantOrder_rightTranslate determinantSlice determinant_mixedEmbedding exists_determinantOrder fiberIntegral fiberIntegral_def fiberIntegral_mixedEmbedding_mul fiberIntegral_mixedSubgroup_mul fiberKernel fiberKernel_comp_zeroSlice_eq fiberKernel_comp_zeroSlice_eq_zeroKernel_comp_slice fiberKernel_compact_ne_top fiberKernel_eq_zero_shift fiberKernel_isSFinite fiberKernel_mk fiberKernel_zero_comp fiberKernel_zero_comp_restrict fiberMeasures_mixedSubgroup_mul fiberPoint_firstBlockEmbedding_mul fiberPoint_mem_determinantSlice_iff fiberPoint_mixedEmbedding_mul fiberPoint_slice_isCompact_preimage firstBlockAverage firstBlockAverage_eq_integral_kernel firstBlockAverage_mk firstBlockEmbedding_mem_mixedSubgroup instBorelSpaceBlockQuotientCarrier instBorelSpaceBlockQuotientCarrier_1 instBorelSpaceGeneralLinearCarrier instBorelSpaceGeneralLinearCarrier_1 instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceLeftUnipotentQuotientCarrier_1 instBorelSpaceMixedQuotient instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instLocallyCompactSpaceGeneralLinearCarrier instLocallyCompactSpaceGeneralLinearCarrier_1 instLocallyCompactSpaceMatrixFinCarrier instLocallyCompactSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instLocallyCompactSpaceSubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceBlockQuotientCarrier instMeasurableSpaceBlockQuotientCarrier_1 instMeasurableSpaceGeneralLinearCarrier instMeasurableSpaceGeneralLinearCarrier_1 instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier_1 instMeasurableSpaceMixedQuotient instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instSecondCountableTopologyGeneralLinearCarrier instSecondCountableTopologyGeneralLinearCarrier_1 instSecondCountableTopologyGeneralLinearCarrier_2 instSecondCountableTopologySubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instSecondCountableTopologySubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instT2SpaceCarrier instT2SpaceCarrier_1 instT2SpaceCarrier_2 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 isClopen_determinantSlice isClosed_mixedSubgroup isOpenEmbedding_normOneSubtype kernelShiftBlockQuotientBorel kernelShiftBlockQuotientMeasurable kernelShiftGLBorel kernelShiftGLMeasurable kernelShiftLocalField kernelShiftMixedBorel kernelShiftMixedMeasurable kernelShiftMixedQuotientBorel kernelShiftMixedQuotientMeasurable kernelShiftSmallQuotientBorel kernelShiftSmallQuotientMeasurable kernelShiftTopology kernelShiftUnipotentBorel kernelShiftUnipotentMeasurable kernelShiftValuativeRel lintegral_blockHaar lintegral_comp_quotientAverageReal lintegral_fiberPoint_quotientAverageReal map_mixedHaar_conjugation map_normOneHaar map_normOneHaar_conjugation map_restrict_mixedLeftShift map_restrict_smallSlice map_restrict_smallSlice_of_ord measurableSet_determinantSlice measurable_fiberMeasures measurePreserving_mixedLeftShift mem_determinantSlice mem_mixedSubgroup_iff mem_mixedSubgroup_iff_determinantNorm mem_normOneSubgroup_iff mem_normOneSubgroup_iff_normalizedAbs mixedCoordinates mixedCoordinates_mixedEmbedding mixedEmbedding mixedEmbedding_apply mixedEmbedding_index_one_one mixedEmbedding_index_one_zero mixedEmbedding_index_zero_one mixedEmbedding_index_zero_zero mixedEmbedding_mem mixedEmbedding_mixedCoordinates mixedFirstQuotient mixedFirstQuotient_block_mul mixedHaar mixedHaar_isHaar mixedHaar_isMulRightInvariant mixedHaar_regular mixedLeftShift mixedLeftShift_mk mixedSubgroup mixedSubgroupEquiv mixedSubgroupEquiv_apply_val mixedSubgroupHomeomorph mixedSubgroup_le_normOneSubgroup mixedSubgroup_le_parabolic mixed_compatibleMeasureExists mk_mem_determinantSlice mul_inv_mem_normOne_of_ord_eq normOneHaar normOneHaar_isHaar normOneHaar_isMulRightInvariant normOneHaar_regular normOneRightInvariant_of_isCompatible normOneSubgroup normalized_tower ord_determinant_eq_zero rightTranslate_mem_determinantSlice sliceShiftFieldT2 sliceShiftGLBorel sliceShiftGLLocallyCompact sliceShiftGLMeasurable sliceShiftGLSecondCountable sliceShiftLocalField sliceShiftMixedBorel sliceShiftMixedLocallyCompact sliceShiftMixedMeasurable sliceShiftMixedQuotientBorel sliceShiftMixedQuotientMeasurable sliceShiftNormOneBorel sliceShiftNormOneLocallyCompact sliceShiftNormOneMeasurable sliceShiftNormOneSecondCountable sliceShiftTopology sliceShiftUnipotentBorel sliceShiftUnipotentLocallyCompact sliceShiftUnipotentMeasurable sliceShiftUnipotentSecondCountable sliceShiftValuativeRel small_orbitKernel_comp_zero towerBlockQuotientLocallyCompact towerBlockQuotientSecondCountable towerBlockQuotientT2 towerInst1 towerInst10 towerInst11 towerInst12 towerInst13 towerInst14 towerInst15 towerInst16 towerInst17 towerInst2 towerInst20 towerInst21 towerInst23 towerInst24 towerInst25 towerInst26 towerInst27 towerInst28 towerInst29 towerInst3 towerInst30 towerInst4 towerInst8 towerInst9 unfoldingInst1 unfoldingInst10 unfoldingInst11 unfoldingInst12 unfoldingInst13 unfoldingInst14 unfoldingInst15 unfoldingInst2 unfoldingInst20 unfoldingInst21 unfoldingInst23 unfoldingInst24 unfoldingInst3 unfoldingInst4 unfoldingInst8 unfoldingInst9
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice
open scoped ENNReal

universe uF

/-- Normalized first-block disintegration over the fixed zero outer determinant slice,
with its s-finite measurable kernel and complete Tonelli and Bochner laws. -/
theorem twoBlockFirstBlockQuotientIntegration :
    TwoBlockFirstBlockQuotientIntegrationStatement.{uF} := by
  intro F _ _ _ _ t m h
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := T.generalLinearTopologicalGroup (t + 1)
  let := T.generalLinearTopologicalGroup (m 0 + 1)
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  let G := GeneralLinear (t + 1) F
  let GA := GeneralLinear (m 0 + 1) F
  let Na := upperUnipotent (m 0 + 1) F
  let Nb := upperUnipotent (m 1 + 1) F
  let A0 := normOneSubgroup F (m 0 + 1)
  let H := TwoBlockUnipotentQuotient.blockUnipotent h F
  let L := mixedSubgroup F h
  let AQ := LeftUnipotentQuotient (m 0) F
  let HQ := TwoBlockUnipotentQuotient.BlockQuotient h F
  let LQ := MixedQuotient F h
  let : SecondCountableTopology GA := T.generalLinearSecondCountableTopology (m 0 + 1)
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : MeasurableSpace GA := borel GA
  let : BorelSpace GA := ⟨rfl⟩
  let : MeasurableSpace A0 := borel A0
  let : BorelSpace A0 := ⟨rfl⟩
  let : SecondCountableTopology A0 := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let : MeasurableSpace L := borel L
  let : BorelSpace L := ⟨rfl⟩
  let : ∀ i : Fin 2, MeasurableSpace (upperUnipotent (m i + 1) F) :=
    fun i => borel (upperUnipotent (m i + 1) F)
  let : ∀ i : Fin 2, BorelSpace (upperUnipotent (m i + 1) F) :=
    fun _ => ⟨rfl⟩
  let : ∀ i : Fin 2, SecondCountableTopology (upperUnipotent (m i + 1) F) :=
    fun i => by
      let := T.generalLinearSecondCountableTopology (m i + 1)
      exact Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : BorelSpace (TwoBlockUnipotentQuotient.BlockUnipotents m F) := inferInstance
  let : BorelSpace (A0 × Nb) := inferInstance
  let : MeasurableSpace AQ := borel AQ
  let : BorelSpace AQ := ⟨rfl⟩
  let : MeasurableSpace HQ := borel HQ
  let : BorelSpace HQ := ⟨rfl⟩
  let : MeasurableSpace LQ := borel LQ
  let : BorelSpace LQ := ⟨rfl⟩
  let μG : Measure G := generalLinearHaar F t
  let μGA : Measure GA := generalLinearHaar F (m 0)
  let μNa : Measure Na := unipotentHaar F (m 0)
  let μH : Measure H := TwoBlockUnipotentQuotient.blockHaar F h
  change μH.IsHaarMeasure ∧ μH.Regular ∧ _
  refine ⟨inferInstance, inferInstance, normOneHaar F (m 0), inferInstance,
    inferInstance, map_normOneHaar F (m 0), ?_⟩
  let μL : Measure L := mixedHaar F h
  change μL.IsHaarMeasure ∧ μL.Regular ∧ _
  have hNa : Measure.IsMulRightInvariant μNa := inferInstance
  have hH : Measure.IsMulRightInvariant μH := inferInstance
  have hL : Measure.IsMulRightInvariant μL := inferInstance
  refine ⟨inferInstance, inferInstance, hNa, hH, hL, ?_⟩
  let := hNa
  let := hH
  let := hL
  refine ⟨TwoBlockUnipotentQuotient.fullUnipotent_compatibleMeasureExists F (m 0),
    TwoBlockUnipotentQuotient.block_compatibleMeasureExists F h,
    mixed_compatibleMeasureExists F h, ?_⟩
  intro νA νH νL hνA hνH hνL
  have hνA' : IsCompatible Na μGA μNa νA := hνA
  have hνH' : IsCompatible H μG μH νH := hνH
  have hνL' : IsCompatible L μG μL νL := hνL
  let := T.generalLinearLocallyCompactSpace (m 0 + 1)
  let := T.generalLinearLocallyCompactSpace (t + 1)
  let := T.generalLinearSecondCountableTopology (t + 1)
  let := leftQuotient_locallyCompactSpace Na
  let := leftQuotient_locallyCompactSpace H
  let := leftQuotient_locallyCompactSpace L
  let := Topology.IsOpenQuotientMap.secondCountableTopology
    (leftQuotient_isOpenQuotientMap Na)
  let := Topology.IsOpenQuotientMap.secondCountableTopology
    (leftQuotient_isOpenQuotientMap H)
  let := Topology.IsOpenQuotientMap.secondCountableTopology
    (leftQuotient_isOpenQuotientMap L)
  let := hνA'.regular
  let := hνH'.regular
  let := hνL'.regular
  have : SigmaFinite νA := inferInstance
  have : SigmaFinite νH := inferInstance
  have : SigmaFinite νL := inferInstance
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  intro k
  let hInvariant := normOneRightInvariant_of_isCompatible F (m 0) μGA μNa νA hνA'
  let κ := fiberKernel F h νA hInvariant k
  have hκfinite : IsSFiniteKernel κ := fiberKernel_isSFinite F h νA hInvariant k
  have hκ : ∀ g : G, κ (Quotient.mk _ g) =
      Measure.map (fun q => fiberPoint h F q g)
        (νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice T (m 0) k)) :=
    fiberKernel_mk F h νA hInvariant k
  have hzero := (normalized_tower F h νA hInvariant hνA' νL hνL' νH hνH').2
  have hcomp : κ ∘ₘ νL.restrict (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.determinantSlice F h 0) =
      νH.restrict (Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.determinantSlice F h k) :=
    fiberKernel_comp_zeroSlice_eq F h νA hInvariant hνA' νL hνL' νH hzero k
  exact ⟨κ, hκfinite, hκ, hcomp,
    analytic_of_comp_eq F h νA hInvariant k κ hκ _ _ hcomp⟩

end Langlands.AllField.RankinSelberg
