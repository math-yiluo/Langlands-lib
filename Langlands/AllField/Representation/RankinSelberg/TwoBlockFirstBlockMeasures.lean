import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockMeasures
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockQuotientData
import Langlands.AllField.Representation.RankinSelberg.TwoBlockUnipotentMeasures
/-!
# Restriction-normalized measures for the first-block quotient

The Haar measure on the norm-one first block is pulled back from the ambient
general linear Haar measure through the open subgroup inclusion. The mixed
subgroup has the transported product Haar measure.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient
open Langlands.RankinSelberg.TwoBlockFirstBlockQuotient hiding MixedQuotient NormOneRightInvariant blockUnipotent_le_mixedSubgroup continuous_determinantOrder continuous_fiberPoint determinantOrder determinantOrder_mk determinantSlice determinant_mixedEmbedding fiberIntegral fiberIntegral_def fiberIntegral_mixedEmbedding_mul fiberIntegral_mixedSubgroup_mul fiberPoint_mem_determinantSlice_iff fiberPoint_mixedEmbedding_mul firstBlockAverage firstBlockAverage_mk instBorelSpaceGeneralLinearCarrier instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instIsNonarchimedeanLocalFieldCarrier instLocallyCompactSpaceMatrixFinCarrier instLocallyCompactSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instLocallyCompactSpaceSubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceGeneralLinearCarrier instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instSecondCountableTopologyGeneralLinearCarrier instSecondCountableTopologySubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instSecondCountableTopologySubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instT2SpaceCarrier instTopologicalSpaceCarrier instValuativeRelCarrier isClopen_determinantSlice isClosed_mixedSubgroup isOpenEmbedding_normOneSubtype map_normOneHaar measurableSet_determinantSlice mem_determinantSlice mem_mixedSubgroup_iff mem_mixedSubgroup_iff_determinantNorm mem_normOneSubgroup_iff mem_normOneSubgroup_iff_normalizedAbs mixedCoordinates mixedCoordinates_mixedEmbedding mixedEmbedding mixedEmbedding_apply mixedEmbedding_index_one_one mixedEmbedding_index_one_zero mixedEmbedding_index_zero_one mixedEmbedding_index_zero_zero mixedEmbedding_mem mixedEmbedding_mixedCoordinates mixedHaar mixedHaar_isHaar mixedHaar_isMulRightInvariant mixedHaar_regular mixedSubgroup mixedSubgroupEquiv mixedSubgroupEquiv_apply_val mixedSubgroupHomeomorph mixedSubgroup_le_normOneSubgroup mixedSubgroup_le_parabolic mixed_compatibleMeasureExists normOneHaar normOneHaar_isHaar normOneHaar_isMulRightInvariant normOneHaar_regular normOneRightInvariant_of_isCompatible normOneSubgroup ord_determinant_eq_zero
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice rightTranslate_mem_determinantSlice

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance (n : ℕ) : MeasurableSpace (GeneralLinear n F) := borel _
local instance (n : ℕ) : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
local instance (n : ℕ) : SecondCountableTopology (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology n
local instance (n : ℕ) : LocallyCompactSpace (Matrix (Fin n) (Fin n) F) :=
  inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → F))
local instance (n : ℕ) : MeasurableSpace (normOneSubgroup F n) := borel _
local instance (n : ℕ) : BorelSpace (normOneSubgroup F n) := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (upperUnipotent n F) := borel _
local instance (n : ℕ) : BorelSpace (upperUnipotent n F) := ⟨rfl⟩
local instance (n : ℕ) : SecondCountableTopology (upperUnipotent n F) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance (n : ℕ) : LocallyCompactSpace (upperUnipotent n F) :=
  UpperUnipotent.locallyCompactSpace

/-- The norm-one subgroup inclusion is an open embedding. -/
theorem isOpenEmbedding_normOneSubtype (n : ℕ) :
    Topology.IsOpenEmbedding (Subtype.val : normOneSubgroup F n → GeneralLinear n F) :=
  ((⟨⟩ : LocalFieldData F).isOpen_ker_determinantNorm n).isOpenEmbedding_subtypeVal

/-- Haar measure on `GL_(n+1)^0`, normalized by restriction from `GL_(n+1)`. -/
def normOneHaar (n : ℕ) : Measure (normOneSubgroup F (n + 1)) :=
  (generalLinearHaar F n).comap Subtype.val

instance normOneHaar_isHaar (n : ℕ) : (normOneHaar F n).IsHaarMeasure :=
  Measure.IsHaarMeasure.comap (generalLinearHaar F n)
    (f := (normOneSubgroup F (n + 1)).subtype) (mH := inferInstance)
    (isOpenEmbedding_normOneSubtype F (n + 1))

instance normOneHaar_regular (n : ℕ) : (normOneHaar F n).Regular :=
  Measure.Regular.comap' (generalLinearHaar F n)
    (isOpenEmbedding_normOneSubtype F (n + 1))

instance normOneHaar_isMulRightInvariant (n : ℕ) :
    (normOneHaar F n).IsMulRightInvariant :=
  Measure.IsMulRightInvariant.comap (generalLinearHaar F n)
    (f := (normOneSubgroup F (n + 1)).subtype)
    (isOpenEmbedding_normOneSubtype F (n + 1)).measurableEmbedding

/-- The normalization is an exact equality of measures. -/
theorem map_normOneHaar (n : ℕ) :
    Measure.map Subtype.val (normOneHaar F n) =
      (generalLinearHaar F n).restrict (normOneSubgroup F (n + 1)) := by
  have he : Set.range (Subtype.val : normOneSubgroup F (n + 1) →
      GeneralLinear (n + 1) F) = (normOneSubgroup F (n + 1) : Set _) := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  exact ((isOpenEmbedding_normOneSubtype F (n + 1)).measurableEmbedding.map_comap
    (generalLinearHaar F n)).trans (congrArg _ he)

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance : MeasurableSpace (mixedSubgroup F h) := borel _
local instance : BorelSpace (mixedSubgroup F h) := ⟨rfl⟩
local instance : SecondCountableTopology (normOneSubgroup F (m 0 + 1)) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance : LocallyCompactSpace (normOneSubgroup F (m 0 + 1)) :=
  (isOpenEmbedding_normOneSubtype F (m 0 + 1)).locallyCompactSpace

/-- Product Haar measure on the actual mixed subgroup. -/
def mixedHaar : Measure (mixedSubgroup F h) :=
  Measure.map (mixedSubgroupEquiv F h)
    ((normOneHaar F (m 0)).prod (unipotentHaar F (m 1)))

instance mixedHaar_isHaar : (mixedHaar F h).IsHaarMeasure := by
  exact (mixedSubgroupHomeomorph F h).isHaarMeasure_map
    ((normOneHaar F (m 0)).prod (unipotentHaar F (m 1)))

instance mixedHaar_regular : (mixedHaar F h).Regular := by
  let K : TopologicalSpace.PositiveCompacts
      (normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F) :=
    Classical.arbitrary _
  have : ((normOneHaar F (m 0)).prod (unipotentHaar F (m 1))).Regular :=
    Measure.regular_of_isMulLeftInvariant K.isCompact K.interior_nonempty
      K.isCompact.measure_ne_top
  exact Measure.Regular.map (mixedSubgroupHomeomorph F h).toHomeomorph

instance mixedHaar_isMulRightInvariant : (mixedHaar F h).IsMulRightInvariant := by
  let e := mixedSubgroupHomeomorph F h
  let μ := (normOneHaar F (m 0)).prod (unipotentHaar F (m 1))
  have hemeas : Measurable
      (e : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F →
        mixedSubgroup F h) := e.continuous.measurable
  change (Measure.map e μ).IsMulRightInvariant
  refine ⟨fun g => ?_⟩
  rw [Measure.map_map (measurable_mul_const g) hemeas]
  have he : (fun x => e x * g) = e ∘ (fun x => x * e.symm g) := by
    funext x
    simp
  change Measure.map (fun x => e x * g) μ = Measure.map e μ
  rw [he, ← Measure.map_map hemeas (measurable_mul_const _), map_mul_right_eq_self]

/-- Compatible quotient existence for the fixed restriction-normalized pair. -/
theorem mixed_compatibleMeasureExists
    [MeasurableSpace (MixedQuotient F h)] [BorelSpace (MixedQuotient F h)] :
    CompatibleMeasureExists (mixedSubgroup F h)
      (generalLinearHaar F t) (mixedHaar F h) :=
  Langlands.QuotientIntegration.compatibleMeasureExists (mixedSubgroup F h)
    (isClosed_mixedSubgroup F h) (generalLinearHaar F t) (mixedHaar F h)

end Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient
