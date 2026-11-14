import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockKernelShift
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockFiberKernel
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockSliceShift
/-!
# Determinant transport for the first-block fiber kernel
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient
open Langlands.RankinSelberg.TwoBlockFirstBlockQuotient hiding MixedQuotient NormOneRightInvariant blockUnipotent_le_mixedSubgroup continuous_determinantOrder continuous_fiberPoint determinantOrder determinantOrder_mixedLeftShift determinantOrder_mk determinantSlice determinant_mixedEmbedding exists_determinantOrder fiberIntegral fiberIntegral_def fiberIntegral_mixedEmbedding_mul fiberIntegral_mixedSubgroup_mul fiberKernel fiberKernel_comp_zeroSlice_eq fiberKernel_comp_zeroSlice_eq_zeroKernel_comp_slice fiberKernel_eq_zero_shift fiberKernel_mk fiberMeasures_mixedSubgroup_mul fiberPoint_firstBlockEmbedding_mul fiberPoint_mem_determinantSlice_iff fiberPoint_mixedEmbedding_mul firstBlockAverage firstBlockAverage_mk instBorelSpaceBlockQuotientCarrier instBorelSpaceGeneralLinearCarrier instBorelSpaceGeneralLinearCarrier_1 instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceMixedQuotient instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instLocallyCompactSpaceGeneralLinearCarrier instLocallyCompactSpaceMatrixFinCarrier instLocallyCompactSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instLocallyCompactSpaceSubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceBlockQuotientCarrier instMeasurableSpaceGeneralLinearCarrier instMeasurableSpaceGeneralLinearCarrier_1 instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceMixedQuotient instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instSecondCountableTopologyGeneralLinearCarrier instSecondCountableTopologyGeneralLinearCarrier_1 instSecondCountableTopologySubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instSecondCountableTopologySubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instT2SpaceCarrier instT2SpaceCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 isClopen_determinantSlice isClosed_mixedSubgroup isOpenEmbedding_normOneSubtype kernelShiftBlockQuotientBorel kernelShiftBlockQuotientMeasurable kernelShiftGLBorel kernelShiftGLMeasurable kernelShiftLocalField kernelShiftMixedBorel kernelShiftMixedMeasurable kernelShiftMixedQuotientBorel kernelShiftMixedQuotientMeasurable kernelShiftSmallQuotientBorel kernelShiftSmallQuotientMeasurable kernelShiftTopology kernelShiftUnipotentBorel kernelShiftUnipotentMeasurable kernelShiftValuativeRel map_mixedHaar_conjugation map_normOneHaar map_normOneHaar_conjugation map_restrict_mixedLeftShift map_restrict_smallSlice map_restrict_smallSlice_of_ord measurableSet_determinantSlice measurable_fiberMeasures measurePreserving_mixedLeftShift mem_determinantSlice mem_mixedSubgroup_iff mem_mixedSubgroup_iff_determinantNorm mem_normOneSubgroup_iff mem_normOneSubgroup_iff_normalizedAbs mixedCoordinates mixedCoordinates_mixedEmbedding mixedEmbedding mixedEmbedding_apply mixedEmbedding_index_one_one mixedEmbedding_index_one_zero mixedEmbedding_index_zero_one mixedEmbedding_index_zero_zero mixedEmbedding_mem mixedEmbedding_mixedCoordinates mixedHaar mixedHaar_isHaar mixedHaar_isMulRightInvariant mixedHaar_regular mixedLeftShift mixedLeftShift_mk mixedSubgroup mixedSubgroupEquiv mixedSubgroupEquiv_apply_val mixedSubgroupHomeomorph mixedSubgroup_le_normOneSubgroup mixedSubgroup_le_parabolic mixed_compatibleMeasureExists normOneHaar normOneHaar_isHaar normOneHaar_isMulRightInvariant normOneHaar_regular normOneRightInvariant_of_isCompatible normOneSubgroup ord_determinant_eq_zero sliceShiftFieldT2 sliceShiftGLBorel sliceShiftGLLocallyCompact sliceShiftGLMeasurable sliceShiftGLSecondCountable sliceShiftLocalField sliceShiftMixedBorel sliceShiftMixedLocallyCompact sliceShiftMixedMeasurable sliceShiftMixedQuotientBorel sliceShiftMixedQuotientMeasurable sliceShiftNormOneBorel sliceShiftNormOneLocallyCompact sliceShiftNormOneMeasurable sliceShiftNormOneSecondCountable sliceShiftTopology sliceShiftUnipotentBorel sliceShiftUnipotentLocallyCompact sliceShiftUnipotentMeasurable sliceShiftUnipotentSecondCountable sliceShiftValuativeRel
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice rightTranslate_mem_determinantSlice

open _root_.MeasureTheory ProbabilityTheory
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open scoped ENNReal

universe uF

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance kernelShiftGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear n F) := borel _
local instance kernelShiftGLBorel (n : ℕ) : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
local instance kernelShiftUnipotentMeasurable (n : ℕ) : MeasurableSpace (upperUnipotent n F) := borel _
local instance kernelShiftUnipotentBorel (n : ℕ) : BorelSpace (upperUnipotent n F) := ⟨rfl⟩
local instance kernelShiftSmallQuotientMeasurable (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n F) := borel _
local instance kernelShiftSmallQuotientBorel (n : ℕ) : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩

/-- Right translation carries the zero small slice to the prescribed slice exactly. -/
theorem map_restrict_smallSlice_of_ord (n : ℕ)
    (νA : Measure (LeftUnipotentQuotient n F))
    (hνA : IsCompatible (upperUnipotent (n + 1) F)
      (generalLinearHaar F n) (unipotentHaar F n) νA)
    (z : GeneralLinear (n + 1) F) (k : ℤ)
    (hz : (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant z : F) = k) :
    Measure.map (rightTranslate _ z)
        (νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) n 0)) =
      νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) n k) := by
  have hpre : rightTranslate _ z ⁻¹'
      Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) n k =
      Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) n 0 := by
    ext q
    rw [Set.mem_preimage,
      Langlands.AllField.RankinSelberg.rightTranslate_mem_determinantSlice (⟨⟩ : LocalFieldData F) n k,
      hz, sub_self]
  have hp := (hνA.right_invariant z).restrict_preimage_emb
    (rightTranslate _ z).measurableEmbedding
    (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) n k)
  rw [hpre] at hp
  exact hp.map_eq

/-- Every integer occurs as the determinant order of a positive-rank matrix. -/
theorem exists_determinantOrder (n : ℕ) (k : ℤ) :
    ∃ z : GeneralLinear (n + 1) F,
      (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant z : F) = k := by
  obtain ⟨x, hx, hxo⟩ := (⟨⟩ : LocalFieldData F).ord_surjective_nonzero k
  obtain ⟨z, hz⟩ := Matrix.GeneralLinearGroup.det_surjective
    (n := Fin (n + 1)) (Units.mk0 x hx)
  refine ⟨z, ?_⟩
  change (⟨⟩ : LocalFieldData F).ord (Matrix.GeneralLinearGroup.det z : F) = k
  rw [hz]
  exact hxo

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance kernelShiftMixedQuotientMeasurable : MeasurableSpace (MixedQuotient F h) := borel _
local instance kernelShiftMixedQuotientBorel : BorelSpace (MixedQuotient F h) := ⟨rfl⟩
local instance kernelShiftBlockQuotientMeasurable : MeasurableSpace (TwoBlockUnipotentQuotient.BlockQuotient h F) :=
  borel _
local instance kernelShiftBlockQuotientBorel : BorelSpace (TwoBlockUnipotentQuotient.BlockQuotient h F) := ⟨rfl⟩
local instance kernelShiftMixedMeasurable : MeasurableSpace (mixedSubgroup F h) := borel _
local instance kernelShiftMixedBorel : BorelSpace (mixedSubgroup F h) := ⟨rfl⟩

/-- Arbitrary first-block multiplication of the base is right translation of the fiber. -/
theorem fiberPoint_firstBlockEmbedding_mul
    (q : LeftUnipotentQuotient (m 0) F)
    (z : GeneralLinear (m 0 + 1) F) (g : GeneralLinear (t + 1) F) :
    fiberPoint h F q (firstBlockEmbedding h F z * g) =
      fiberPoint h F (rightTranslate _ z q) g := by
  induction q using Quotient.inductionOn with
  | h u => rw [rightTranslate_mk, fiberPoint_mk, fiberPoint_mk, map_mul, mul_assoc]

variable (νA : Measure (LeftUnipotentQuotient (m 0) F)) [SFinite νA]
  (hInvariant : NormOneRightInvariant F (m 0) νA)
  (hνA : IsCompatible (upperUnipotent (m 0 + 1) F)
    (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) νA)

include hνA

/-- The k-th fiber kernel is the zero kernel evaluated at the shifted outer point. -/
theorem fiberKernel_eq_zero_shift (z : GeneralLinear (m 0 + 1) F) (k : ℤ)
    (hz : (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant z : F) = k)
    (q : MixedQuotient F h) :
    fiberKernel F h νA hInvariant k q =
      fiberKernel F h νA hInvariant 0 (mixedLeftShift F h z q) := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [mixedLeftShift_mk, fiberKernel_mk, fiberKernel_mk]
    have hf : Measurable (fun q => fiberPoint h F q g) :=
      ((continuous_fiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
    simp_rw [fiberPoint_firstBlockEmbedding_mul]
    change _ = Measure.map ((fun q => fiberPoint h F q g) ∘ rightTranslate _ z) _
    rw [← Measure.map_map hf (rightTranslate _ z).measurable,
      map_restrict_smallSlice_of_ord F (m 0) νA hνA z k hz]

/-- Kernel composition transports the inner k slice to the outer k slice. -/
theorem fiberKernel_comp_zeroSlice_eq_zeroKernel_comp_slice
    (νL : Measure (MixedQuotient F h))
    (hνL : IsCompatible (mixedSubgroup F h)
      (generalLinearHaar F t) (mixedHaar F h) νL) (k : ℤ) :
    fiberKernel F h νA hInvariant k ∘ₘ (νL.restrict (determinantSlice F h 0)) =
      fiberKernel F h νA hInvariant 0 ∘ₘ (νL.restrict (determinantSlice F h k)) := by
  obtain ⟨z, hz⟩ := exists_determinantOrder F (m 0) k
  rw [← map_restrict_mixedLeftShift F h νL hνL z k hz]
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe _ hs) (mixedLeftShift F h z).measurable]
  apply lintegral_congr
  intro q
  rw [fiberKernel_eq_zero_shift F h νA hInvariant hνA z k hz]

/-- The all-slices conclusion follows from zero-kernel disintegration on each outer slice. -/
theorem fiberKernel_comp_zeroSlice_eq
    (νL : Measure (MixedQuotient F h))
    (hνL : IsCompatible (mixedSubgroup F h)
      (generalLinearHaar F t) (mixedHaar F h) νL)
    (νH : Measure (TwoBlockUnipotentQuotient.BlockQuotient h F))
    (hzero : ∀ k : ℤ, fiberKernel F h νA hInvariant 0 ∘ₘ
      (νL.restrict (determinantSlice F h k)) =
        νH.restrict (Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.determinantSlice F h k)) (k : ℤ) :
    fiberKernel F h νA hInvariant k ∘ₘ (νL.restrict (determinantSlice F h 0)) =
      νH.restrict (Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.determinantSlice F h k) := by
  rw [fiberKernel_comp_zeroSlice_eq_zeroKernel_comp_slice F h νA hInvariant hνA νL hνL k,
    hzero k]

end Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient
