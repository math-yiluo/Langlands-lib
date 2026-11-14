import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockFiberKernel
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockMeasures
/-!
# The first-block slice fiber kernel

Construct the measurable kernel with the prescribed everywhere representative
formula, using right translation on the small quotient for descent.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient
open Langlands.RankinSelberg.TwoBlockFirstBlockQuotient hiding MixedQuotient NormOneRightInvariant blockUnipotent_le_mixedSubgroup continuous_determinantOrder continuous_fiberPoint determinantOrder determinantOrder_mk determinantSlice determinant_mixedEmbedding fiberIntegral fiberIntegral_def fiberIntegral_mixedEmbedding_mul fiberIntegral_mixedSubgroup_mul fiberKernel fiberKernel_mk fiberMeasures_mixedSubgroup_mul fiberPoint_mem_determinantSlice_iff fiberPoint_mixedEmbedding_mul firstBlockAverage firstBlockAverage_mk instBorelSpaceBlockQuotientCarrier instBorelSpaceGeneralLinearCarrier instBorelSpaceGeneralLinearCarrier_1 instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceMixedQuotient instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instLocallyCompactSpaceGeneralLinearCarrier instLocallyCompactSpaceMatrixFinCarrier instLocallyCompactSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instLocallyCompactSpaceSubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceBlockQuotientCarrier instMeasurableSpaceGeneralLinearCarrier instMeasurableSpaceGeneralLinearCarrier_1 instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceMixedQuotient instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instSecondCountableTopologyGeneralLinearCarrier instSecondCountableTopologyGeneralLinearCarrier_1 instSecondCountableTopologySubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instSecondCountableTopologySubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instT2SpaceCarrier instT2SpaceCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 isClopen_determinantSlice isClosed_mixedSubgroup isOpenEmbedding_normOneSubtype map_normOneHaar map_restrict_smallSlice measurableSet_determinantSlice measurable_fiberMeasures mem_determinantSlice mem_mixedSubgroup_iff mem_mixedSubgroup_iff_determinantNorm mem_normOneSubgroup_iff mem_normOneSubgroup_iff_normalizedAbs mixedCoordinates mixedCoordinates_mixedEmbedding mixedEmbedding mixedEmbedding_apply mixedEmbedding_index_one_one mixedEmbedding_index_one_zero mixedEmbedding_index_zero_one mixedEmbedding_index_zero_zero mixedEmbedding_mem mixedEmbedding_mixedCoordinates mixedHaar mixedHaar_isHaar mixedHaar_isMulRightInvariant mixedHaar_regular mixedSubgroup mixedSubgroupEquiv mixedSubgroupEquiv_apply_val mixedSubgroupHomeomorph mixedSubgroup_le_normOneSubgroup mixedSubgroup_le_parabolic mixed_compatibleMeasureExists normOneHaar normOneHaar_isHaar normOneHaar_isMulRightInvariant normOneHaar_regular normOneRightInvariant_of_isCompatible normOneSubgroup ord_determinant_eq_zero
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice rightTranslate_mem_determinantSlice

open _root_.MeasureTheory ProbabilityTheory
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance (n : ℕ) : MeasurableSpace (GeneralLinear n F) := borel _
local instance (n : ℕ) : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
local instance (n : ℕ) : SecondCountableTopology (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology n
local instance (n : ℕ) : LocallyCompactSpace (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace n
local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n F) := borel _
local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
local instance : MeasurableSpace (TwoBlockUnipotentQuotient.BlockQuotient h F) :=
  borel _
local instance : BorelSpace (TwoBlockUnipotentQuotient.BlockQuotient h F) := ⟨rfl⟩
local instance : MeasurableSpace (MixedQuotient F h) := borel _
local instance : BorelSpace (MixedQuotient F h) := ⟨rfl⟩

variable (νA : Measure (LeftUnipotentQuotient (m 0) F)) [SFinite νA]
  (hνA : NormOneRightInvariant F (m 0) νA)

omit [SFinite νA] in
include hνA in
/-- Right translation by a norm-one matrix preserves each restricted small measure. -/
theorem map_restrict_smallSlice (k : ℤ) (u : normOneSubgroup F (m 0 + 1)) :
    Measure.map (rightTranslate _ u.val)
        (νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k)) =
      νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k) := by
  have hS : rightTranslate _ u.val ⁻¹'
      Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k =
      Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k := by
    ext q
    rw [Set.mem_preimage,
      Langlands.AllField.RankinSelberg.rightTranslate_mem_determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k,
      ord_determinant_eq_zero F u.property, sub_zero]
  have hp := (hνA u).restrict_preimage_emb (rightTranslate _ u.val).measurableEmbedding
    (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k)
  rw [hS] at hp
  exact hp.map_eq

/-- Joint continuity and s-finiteness of the small measure give measurable fiber measures. -/
theorem measurable_fiberMeasures (k : ℤ) :
    Measurable (fun g => Measure.map (fun q => fiberPoint h F q g)
      (νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k))) := by
  let := _root_.Topology.IsOpenQuotientMap.secondCountableTopology
    (leftQuotient_isOpenQuotientMap (upperUnipotent (m 0 + 1) F))
  let μ := νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k)
  have hf := (continuous_fiberPoint F h).measurable
  have hm := (Measure.measurable_map _ hf).comp (Measurable.map_prodMk_right (μ := μ))
  simpa only [μ, Measure.map_map hf measurable_prodMk_right, Function.comp_def,
    Function.uncurry_apply_pair] using hm

omit [SFinite νA] in
include hνA in
/-- Left multiplication from the mixed subgroup preserves the representative measures. -/
theorem fiberMeasures_mixedSubgroup_mul (k : ℤ) (l : mixedSubgroup F h)
    (g : GeneralLinear (t + 1) F) :
    Measure.map (fun q => fiberPoint h F q (l.val * g))
        (νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k)) =
      Measure.map (fun q => fiberPoint h F q g)
        (νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k)) := by
  obtain ⟨⟨u, n⟩, hl⟩ := l.property
  have hf : Measurable (fun q => fiberPoint h F q g) :=
    ((continuous_fiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
  rw [← hl]
  simp only [fiberPoint_mixedEmbedding_mul F h]
  change Measure.map ((fun q => fiberPoint h F q g) ∘ rightTranslate _ u.val) _ = _
  rw [← Measure.map_map hf (rightTranslate _ u.val).measurable,
    map_restrict_smallSlice F νA hνA k u]

/-- The actual descended slice kernel, with no extra scalar. -/
def fiberKernel (k : ℤ) :
    Kernel (MixedQuotient F h) (TwoBlockUnipotentQuotient.BlockQuotient h F) := by
  let κ := descend (mixedSubgroup F h)
    (fun g => Measure.map (fun q => fiberPoint h F q g)
      (νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k)))
    (fiberMeasures_mixedSubgroup_mul F h νA hνA k)
  exact ⟨κ, (measurable_quotient_iff _ (isClosed_mixedSubgroup F h) κ).2
    (measurable_fiberMeasures F h νA k)⟩

/-- The representative formula holds for every ambient group element. -/
theorem fiberKernel_mk (k : ℤ) (g : GeneralLinear (t + 1) F) :
    fiberKernel F h νA hνA k (Quotient.mk _ g) =
      Measure.map (fun q => fiberPoint h F q g)
        (νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k)) :=
  rfl

end Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient
