import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockSliceAnalysis
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockDensity
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockFiberProper
import Langlands.AllField.Representation.RankinSelberg.TwoBlockUnipotentQuotientAnalysis
/-!
# Analytic consequences of the lower first-block slice tower

The exact density-scaled slice measure identity is an explicit premise here.
It implies the complete analytic laws for the actual unweighted average.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
open Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient hiding FirstBlockDensityStatement FirstBlockSliceIntegrationStatement LowerMixedQuotient continuous_determinantOrder continuous_firstBlockFiberPoint continuous_lowerMixedFirstQuotient continuous_projectionFromLower continuous_projectionFromMixed continuous_radicalFiberPoint continuous_rightRadicalCoord determinantOrder determinantOrder_mk determinantOrder_projectionFromLower determinantOrder_projectionFromMixed determinantOrder_radicalFiberPoint determinantSlice firstBlockAverage firstBlockAverage_eq_integral_firstBlockKernel firstBlockAverage_mk firstBlockDensity firstBlockEmbedding_mul_lowerRadical_mul_mixedEmbedding firstBlockFiberIntegral firstBlockFiberIntegral_def firstBlockFiberIntegral_lowerMixedSubgroup_mul firstBlockFiberIntegral_lowerRadical_mixedEmbedding_mul firstBlockFiberMeasures_lowerMixed_mul firstBlockFiberPoint firstBlockFiberPoint_lowerRadical_mixedEmbedding_mul firstBlockFiberPoint_mk firstBlockFiberPoint_slice_isCompact_preimage firstBlockKernel firstBlockKernel_compact_ne_top firstBlockKernel_isSFinite firstBlockKernel_mk firstBlockSliceIntegration_of_comp instBorelSpaceCarrier instBorelSpaceCarrier_1 instBorelSpaceGeneralLinearCarrier instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceLeftUnipotentQuotientCarrier_1 instBorelSpaceLowerMixedQuotient instBorelSpaceLowerQuotientCarrier instBorelSpaceLowerQuotientCarrier_1 instBorelSpaceMixedQuotient instBorelSpaceMixedQuotient_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instLocallyCompactSpaceGeneralLinearCarrier instLocallyCompactSpaceGeneralLinearCarrier_1 instLocallyCompactSpaceMatrixFinCarrier instMeasurableSpaceCarrier instMeasurableSpaceCarrier_1 instMeasurableSpaceGeneralLinearCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier_1 instMeasurableSpaceLowerMixedQuotient instMeasurableSpaceLowerQuotientCarrier instMeasurableSpaceLowerQuotientCarrier_1 instMeasurableSpaceMixedQuotient instMeasurableSpaceMixedQuotient_1 instSecondCountableTopologyCarrier instSecondCountableTopologyCarrier_1 instSecondCountableTopologyGeneralLinearCarrier instSecondCountableTopologyGeneralLinearCarrier_1 instSecondCountableTopologyMatrixFinCarrier instT2SpaceCarrier instT2SpaceCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 integral_comp_radicalChange isClopen_determinantSlice isClosed_lowerMixedSubgroup lowerBlockUnipotent_le_lowerMixedSubgroup lowerMixedCoordinates lowerMixedCoordinates_lowerProduct lowerMixedDiagonal lowerMixedDiagonal_fst_val lowerMixedDiagonal_lowerProduct lowerMixedDiagonal_snd_val lowerMixedFirstQuotient lowerMixedFirstQuotient_lower_mul lowerMixedSubgroup lowerMixedSubgroupEquiv lowerMixedSubgroupEquiv_apply_val lowerMixedSubgroupEquiv_mul lowerMixedSubgroupEquiv_symm_apply_fst lowerMixedSubgroupHomeomorph lowerMixedSubgroup_le_normOneSubgroup lowerMixedSubgroup_le_oppositeParabolic lowerMixed_decomposition lowerProduct_lowerMixedCoordinates lowerProduct_mem lowerRadical_mul_leviEmbedding_one_mem lowerSliceAnalysisInstance01 lowerSliceAnalysisInstance36 lowerSliceAnalysisInstance38 lowerSliceAnalysisInstance39 lowerSliceAnalysisInstance40 lowerSliceAnalysisInstance41 measurableSet_determinantSlice measurable_firstBlockFiberMeasures measurable_radicalFiberMeasures measurePreserving_radicalChange mem_lowerMixedSubgroup_iff mixedSubgroup_le_lowerMixedSubgroup mk_mem_determinantSlice projectionFromLower projectionFromLower_mk projectionFromLower_preimage_determinantSlice projectionFromMixed projectionFromMixed_mk projectionFromMixed_preimage_determinantSlice radicalAverage radicalAverage_mk radicalChange radicalChangeHomeomorph radicalChangeHomeomorph_apply radicalChange_apply radicalFiberIntegral radicalFiberIntegral_def radicalFiberIntegral_lowerMixedSubgroup_mul radicalFiberIntegral_lowerRadical_mixedEmbedding_mul radicalFiberMeasures_lowerMixed_mul radicalFiberPoint radicalFiberPoint_def radicalFiberPoint_isCompact_preimage radicalFiberPoint_lowerRadical_mixedEmbedding_mul radicalFiberPoint_mem_determinantSlice_iff radicalKernel radicalKernel_compact_ne_top radicalKernel_isSFinite radicalKernel_mk rightRadicalCoord rightRadicalCoord_mixed_mul_radical
open Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt TwoBlockUnipotentQuotientIntegrationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
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

local instance lowerSliceAnalysisInstance04 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance lowerSliceAnalysisInstance05 : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance lowerSliceAnalysisInstance06 : MeasurableSpace F := borel _
local instance lowerSliceAnalysisInstance07 : BorelSpace F := ⟨rfl⟩
local instance lowerSliceAnalysisInstance08 (a b : ℕ) : LocallyCompactSpace (Matrix (Fin b) (Fin a) F) :=
  inferInstanceAs (LocallyCompactSpace (Fin b → Fin a → F))
local instance lowerSliceAnalysisInstance09 (a b : ℕ) : SecondCountableTopology (Matrix (Fin b) (Fin a) F) :=
  inferInstanceAs (SecondCountableTopology (Fin b → Fin a → F))
local instance lowerSliceAnalysisInstance10 (n : ℕ) : IsTopologicalGroup (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup n
local instance lowerSliceAnalysisInstance11 (n : ℕ) : MeasurableSpace (GeneralLinear n F) := borel _
local instance lowerSliceAnalysisInstance12 (n : ℕ) : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
local instance lowerSliceAnalysisInstance13 (n : ℕ) : SecondCountableTopology (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology n
local instance lowerSliceAnalysisInstance14 (n : ℕ) : LocallyCompactSpace (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace n
local instance lowerSliceAnalysisInstance15 (n : ℕ) : MeasurableSpace (normOneSubgroup F n) := borel _
local instance lowerSliceAnalysisInstance16 (n : ℕ) : BorelSpace (normOneSubgroup F n) := ⟨rfl⟩
local instance lowerSliceAnalysisInstance17 (n : ℕ) : SecondCountableTopology (normOneSubgroup F n) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerSliceAnalysisInstance18 (n : ℕ) : LocallyCompactSpace (normOneSubgroup F n) :=
  (isOpenEmbedding_normOneSubtype F n).locallyCompactSpace
local instance lowerSliceAnalysisInstance19 (n : ℕ) : MeasurableSpace (upperUnipotent n F) := borel _
local instance lowerSliceAnalysisInstance20 (n : ℕ) : BorelSpace (upperUnipotent n F) := ⟨rfl⟩
local instance lowerSliceAnalysisInstance21 (n : ℕ) : SecondCountableTopology (upperUnipotent n F) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerSliceAnalysisInstance22 (n : ℕ) : LocallyCompactSpace (upperUnipotent n F) :=
  UpperUnipotent.locallyCompactSpace
local instance lowerSliceAnalysisInstance23 : MeasurableSpace (lowerMixedSubgroup F h) := borel _
local instance lowerSliceAnalysisInstance24 : BorelSpace (lowerMixedSubgroup F h) := ⟨rfl⟩
local instance lowerSliceAnalysisInstance25 : SecondCountableTopology (lowerMixedSubgroup F h) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerSliceAnalysisInstance26 : LocallyCompactSpace (lowerMixedSubgroup F h) :=
  (isClosed_lowerMixedSubgroup F h).locallyCompactSpace

local notation "R" => Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F
local notation "D" => normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F
local notation "μD" => Measure.prod (normOneHaar F (m 0)) (unipotentHaar F (m 1))

local instance lowerSliceAnalysisInstance27 : MeasurableSpace (mixedSubgroup F h) := borel _
local instance lowerSliceAnalysisInstance28 : BorelSpace (mixedSubgroup F h) := ⟨rfl⟩
local instance lowerSliceAnalysisInstance29 : SecondCountableTopology (mixedSubgroup F h) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerSliceAnalysisInstance30 : LocallyCompactSpace (mixedSubgroup F h) :=
  (isClosed_mixedSubgroup F h).locallyCompactSpace
local instance lowerSliceAnalysisInstance31 : MeasurableSpace (MixedQuotient F h) := borel _
local instance lowerSliceAnalysisInstance32 : BorelSpace (MixedQuotient F h) := ⟨rfl⟩
local instance lowerSliceAnalysisInstance33 : T2Space (MixedQuotient F h) :=
  leftQuotient_t2Space _ (isClosed_mixedSubgroup F h)
local instance lowerSliceAnalysisInstance34 : LocallyCompactSpace (MixedQuotient F h) := leftQuotient_locallyCompactSpace _
local instance lowerSliceAnalysisInstance35 : SecondCountableTopology (MixedQuotient F h) :=
  Topology.IsOpenQuotientMap.secondCountableTopology (leftQuotient_isOpenQuotientMap _)
local instance lowerSliceAnalysisInstance36 : MeasurableSpace (LowerMixedQuotient F h) := borel _
local instance lowerSliceAnalysisInstance37 : BorelSpace (LowerMixedQuotient F h) := ⟨rfl⟩

local instance lowerSliceAnalysisInstance38 (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F) := borel _
local instance lowerSliceAnalysisInstance39 (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
local instance lowerSliceAnalysisInstance40 :
    MeasurableSpace (LowerQuotient h F) := borel _
local instance lowerSliceAnalysisInstance41 :
    BorelSpace (LowerQuotient h F) := ⟨rfl⟩

/-- The published unweighted first-block slice average is the actual kernel
integral at every lower mixed quotient point. -/
theorem firstBlockAverage_eq_integral_firstBlockKernel
    (νA : Measure (LeftUnipotentQuotient (m 0) F)) [SFinite νA]
    (hνA : NormOneRightInvariant F (m 0) νA) (k : ℤ)
    (f : LowerQuotient h F → ℂ) (hf : Measurable f) :
    firstBlockAverage F h νA hνA k f =
      fun q => ∫ z, f z ∂firstBlockKernel F h νA hνA k q := by
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    have hfm : Measurable (fun z => firstBlockFiberPoint F h z g) :=
      ((continuous_firstBlockFiberPoint F h).comp
        (continuous_id.prodMk continuous_const)).measurable
    rw [firstBlockAverage_mk, firstBlockKernel_mk,
      integral_map hfm.aemeasurable hf.aestronglyMeasurable]

/-- The complete first-block conclusions on one small determinant slice and
the zero outer slice. -/
abbrev FirstBlockSliceIntegrationStatement
    (νA : Measure (LeftUnipotentQuotient (m 0) F))
    (hνA : NormOneRightInvariant F (m 0) νA)
    (νL : Measure (LowerMixedQuotient F h))
    (νMinus : Measure (LowerQuotient h F)) (k : ℤ) : Prop :=
  let T := (⟨⟩ : LocalFieldData F)
  let b := m 1 + 1
  let AQk := Langlands.AllField.RankinSelberg.determinantSlice T (m 0) k
  let νL0 := νL.restrict (determinantSlice F h 0)
  let νMinusk := νMinus.restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k)
  let d : ℝ≥0∞ := ENNReal.ofReal ((T.residueCardinality : ℝ) ^ (-(k * (b : ℤ))))
  0 < d ∧ d < ⊤ ∧
  (∀ v : GeneralLinear (m 0 + 1) F,
    (Quotient.mk _ v : LeftUnipotentQuotient (m 0) F) ∈ AQk →
      d = (ENNReal.ofReal (T.normalizedAbs
        (GeneralLinear.determinant v : F))) ^ b) ∧
  ∃ (κA : Kernel (LowerMixedQuotient F h) (LowerQuotient h F))
    (_hκA : IsSFiniteKernel κA),
    (∀ g : GeneralLinear (t + 1) F, κA (Quotient.mk _ g) =
      Measure.map (fun q => firstBlockFiberPoint F h q g) (νA.restrict AQk)) ∧
    (d • (κA ∘ₘ νL0) = νMinusk) ∧
    (∀ f : LowerQuotient h F → ℝ≥0∞, Measurable f →
      (∫⁻ z, f z ∂νMinusk) = d * ∫⁻ q, ∫⁻ z, f z ∂κA q ∂νL0) ∧
    (∀ f : LowerQuotient h F → ℂ, Measurable f →
      (Integrable f νMinusk ↔
        (∀ᵐ q ∂νL0, Integrable f (κA q)) ∧
        Integrable (fun q => ∫ z, ‖f z‖ ∂κA q) νL0) ∧
      (Integrable f νMinusk →
        AEStronglyMeasurable (firstBlockAverage F h νA hνA k f) νL0 ∧
        Integrable (firstBlockAverage F h νA hνA k f) νL0 ∧
        (∫ z, f z ∂νMinusk) = d.toReal •
          ∫ q, firstBlockAverage F h νA hνA k f q ∂νL0))

/-- The exact density-scaled slice tower implies Tonelli, genuine absolute
integrability, and the Bochner law for the actual first-block slice average. -/
theorem firstBlockSliceIntegration_of_comp
    (νA : Measure (LeftUnipotentQuotient (m 0) F)) [SFinite νA]
    [IsFiniteMeasureOnCompacts νA] (hνA : NormOneRightInvariant F (m 0) νA)
    (νL : Measure (LowerMixedQuotient F h))
    (νMinus : Measure (LowerQuotient h F)) (k : ℤ)
    (hcomp : ENNReal.ofReal
      (((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^ (-(k * ((m 1 + 1 : ℕ) : ℤ)))) •
        (firstBlockKernel F h νA hνA k ∘ₘ νL.restrict (determinantSlice F h 0)) =
      νMinus.restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k)) :
    FirstBlockSliceIntegrationStatement F h νA hνA νL νMinus k := by
  obtain ⟨hd0, hdT, hdet⟩ := firstBlockDensity F (m 0) (m 1 + 1) k
  let : IsSFiniteKernel (firstBlockKernel F h νA hνA k) :=
    firstBlockKernel_isSFinite F h νA hνA k
  refine ⟨hd0, hdT, hdet, firstBlockKernel F h νA hνA k, inferInstance,
    firstBlockKernel_mk F h νA hνA k, hcomp, ?_, ?_⟩
  · intro f hf
    rw [← hcomp, lintegral_smul_measure,
      Measure.lintegral_bind (firstBlockKernel F h νA hνA k).measurable.aemeasurable
        hf.aemeasurable]
    rfl
  · intro f hf
    refine ⟨?_, ?_⟩
    · rw [← hcomp, integrable_smul_measure hd0.ne' hdT.ne]
      exact Measure.integrable_comp_iff hf.aestronglyMeasurable
    · intro hfi
      rw [firstBlockAverage_eq_integral_firstBlockKernel F h νA hνA k f hf]
      have hfiComp : Integrable f
          (firstBlockKernel F h νA hνA k ∘ₘ νL.restrict (determinantSlice F h 0)) := by
        apply (integrable_smul_measure hd0.ne' hdT.ne).mp
        rwa [hcomp]
      rw [Measure.comp_eq_comp_const_apply] at hfiComp
      have hi : Integrable (fun q => ∫ z, f z ∂firstBlockKernel F h νA hνA k q)
          (νL.restrict (determinantSlice F h 0)) := by
        simpa using hfiComp.integral_comp
      refine ⟨hi.aestronglyMeasurable, hi, ?_⟩
      rw [← hcomp, integral_smul_measure, Measure.comp_eq_comp_const_apply,
        Kernel.integral_comp hfiComp]
      simp

end Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
