import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockQuotientUnfolding
import Langlands.AllField.Representation.RankinSelberg.EqualRankLastRowReductionProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockMeasures
noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient
open Langlands.RankinSelberg.TwoBlockFirstBlockQuotient hiding MixedQuotient NormOneRightInvariant blockUnipotent_le_mixedSubgroup continuous_determinantOrder continuous_fiberPoint determinantOrder determinantOrder_mk determinantSlice determinant_mixedEmbedding fiberIntegral fiberIntegral_def fiberIntegral_mixedEmbedding_mul fiberIntegral_mixedSubgroup_mul fiberPoint_mem_determinantSlice_iff fiberPoint_mixedEmbedding_mul firstBlockAverage firstBlockAverage_mk instBorelSpaceGeneralLinearCarrier instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instIsNonarchimedeanLocalFieldCarrier instLocallyCompactSpaceMatrixFinCarrier instLocallyCompactSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instLocallyCompactSpaceSubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceGeneralLinearCarrier instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instSecondCountableTopologyGeneralLinearCarrier instSecondCountableTopologySubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instSecondCountableTopologySubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instT2SpaceCarrier instTopologicalSpaceCarrier instValuativeRelCarrier isClopen_determinantSlice isClosed_mixedSubgroup isOpenEmbedding_normOneSubtype lintegral_blockHaar map_normOneHaar measurableSet_determinantSlice mem_determinantSlice mem_mixedSubgroup_iff mem_mixedSubgroup_iff_determinantNorm mem_normOneSubgroup_iff mem_normOneSubgroup_iff_normalizedAbs mixedCoordinates mixedCoordinates_mixedEmbedding mixedEmbedding mixedEmbedding_apply mixedEmbedding_index_one_one mixedEmbedding_index_one_zero mixedEmbedding_index_zero_one mixedEmbedding_index_zero_zero mixedEmbedding_mem mixedEmbedding_mixedCoordinates mixedHaar mixedHaar_isHaar mixedHaar_isMulRightInvariant mixedHaar_regular mixedSubgroup mixedSubgroupEquiv mixedSubgroupEquiv_apply_val mixedSubgroupHomeomorph mixedSubgroup_le_normOneSubgroup mixedSubgroup_le_parabolic mixed_compatibleMeasureExists normOneHaar normOneHaar_isHaar normOneHaar_isMulRightInvariant normOneHaar_regular normOneRightInvariant_of_isCompatible normOneSubgroup ord_determinant_eq_zero small_orbitKernel_comp_zero unfoldingInst1 unfoldingInst10 unfoldingInst11 unfoldingInst12 unfoldingInst13 unfoldingInst14 unfoldingInst15 unfoldingInst2 unfoldingInst20 unfoldingInst21 unfoldingInst23 unfoldingInst24 unfoldingInst3 unfoldingInst4 unfoldingInst8 unfoldingInst9
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankLastRowReductionStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankLastRowReduction equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice rightTranslate_mem_determinantSlice

open _root_.MeasureTheory ProbabilityTheory
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open scoped ENNReal CompactlySupported ProbabilityTheory

universe uF

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance unfoldingInst4 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance unfoldingInst5 : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance unfoldingInst6 : MeasurableSpace F := borel _
local instance unfoldingInst7 : BorelSpace F := ⟨rfl⟩
local instance unfoldingInst8 (n : ℕ) : MeasurableSpace (GeneralLinear n F) := borel _
local instance unfoldingInst9 (n : ℕ) : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
local instance unfoldingInst10 (n : ℕ) : SecondCountableTopology (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology n
local instance unfoldingInst11 (n : ℕ) : LocallyCompactSpace (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace n
local instance unfoldingInst12 (n : ℕ) : MeasurableSpace (upperUnipotent n F) := borel _
local instance unfoldingInst13 (n : ℕ) : BorelSpace (upperUnipotent n F) := ⟨rfl⟩
local instance unfoldingInst14 (n : ℕ) : SecondCountableTopology (upperUnipotent n F) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance unfoldingInst15 (n : ℕ) : LocallyCompactSpace (upperUnipotent n F) :=
  UpperUnipotent.locallyCompactSpace
local instance unfoldingInst16 (n : ℕ) : MeasurableSpace (normOneSubgroup F n) := borel _
local instance unfoldingInst17 (n : ℕ) : BorelSpace (normOneSubgroup F n) := ⟨rfl⟩
local instance unfoldingInst18 (n : ℕ) : SecondCountableTopology (normOneSubgroup F n) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance unfoldingInst19 (n : ℕ) : LocallyCompactSpace (normOneSubgroup F n) :=
  (isOpenEmbedding_normOneSubtype F n).locallyCompactSpace
local instance unfoldingInst20 (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n F) := borel _
local instance unfoldingInst21 (n : ℕ) : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
local instance unfoldingInst22 (n : ℕ) : SecondCountableTopology (LeftUnipotentQuotient n F) :=
  Topology.IsOpenQuotientMap.secondCountableTopology (leftQuotient_isOpenQuotientMap _)
local instance unfoldingInst23 : MeasurableSpace (TwoBlockUnipotentQuotient.blockUnipotent h F) := borel _
local instance unfoldingInst24 : BorelSpace (TwoBlockUnipotentQuotient.blockUnipotent h F) := ⟨rfl⟩
local instance unfoldingInst25 : MeasurableSpace (TwoBlockUnipotentQuotient.BlockQuotient h F) := borel _
local instance unfoldingInst26 : BorelSpace (TwoBlockUnipotentQuotient.BlockQuotient h F) := ⟨rfl⟩
local instance unfoldingInst27 : MeasurableSpace (mixedSubgroup F h) := borel _
local instance unfoldingInst28 : BorelSpace (mixedSubgroup F h) := ⟨rfl⟩
local instance unfoldingInst29 : MeasurableSpace (MixedQuotient F h) := borel _
local instance unfoldingInst30 : BorelSpace (MixedQuotient F h) := ⟨rfl⟩

theorem small_orbitKernel_comp_zero (n : ℕ)
    (νA : Measure (LeftUnipotentQuotient n F))
    (hνA : IsCompatible (upperUnipotent (n + 1) F)
      (generalLinearHaar F n) (unipotentHaar F n) νA) :
    orbitKernel (upperUnipotent (n + 1) F) (UpperUnipotent.isClosed (R := F))
        (unipotentHaar F n) ∘ₘ
      νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) n 0) =
        Measure.map Subtype.val (normOneHaar F n) := by
  let N := upperUnipotent (n + 1) F
  let κ := orbitKernel N (UpperUnipotent.isClosed (R := F)) (unipotentHaar F n)
  let s := Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) n 0
  let π : GeneralLinear (n + 1) F → LeftUnipotentQuotient n F := Quotient.mk _
  have hs : MeasurableSet s := Langlands.AllField.RankinSelberg.isClosed_determinantSlice _ n 0 |>.measurableSet
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
  have hs0 : π ⁻¹' s = (normOneSubgroup F (n + 1) : Set _) := by
    ext u
    change (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant u : F) = 0 ↔ _
    rw [Langlands.LocalFieldData.ord_eq_zero_iff_normalizedAbs,
      Matrix.GeneralLinearGroup.val_det_apply,
      ← mem_normOneSubgroup_iff_normalizedAbs]
    rfl
  rw [map_normOneHaar, ← hs0]
  exact hcomp

/-- The fixed block measure unfolds into its two specified unipotent measures. -/
theorem lintegral_blockHaar (f : TwoBlockUnipotentQuotient.blockUnipotent h F → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ b, f b ∂TwoBlockUnipotentQuotient.blockHaar F h =
      ∫⁻ a : upperUnipotent (m 0 + 1) F,
        ∫⁻ b : upperUnipotent (m 1 + 1) F,
          f (TwoBlockUnipotentQuotient.blockUnipotentEquiv h F
            ((MeasurableEquiv.piFinTwo _).symm (a, b)))
          ∂unipotentHaar F (m 1) ∂unipotentHaar F (m 0) := by
  let e := MeasurableEquiv.piFinTwo (fun i : Fin 2 => upperUnipotent (m i + 1) F)
  have hm : Measurable (TwoBlockUnipotentQuotient.blockUnipotentEquiv h F) :=
    (TwoBlockUnipotentQuotient.blockUnipotentHomeomorph h F).continuous.measurable
  rw [TwoBlockUnipotentQuotient.blockHaar, lintegral_map hf hm]
  have hpi := measurePreserving_piFinTwo (fun i : Fin 2 => unipotentHaar F (m i))
  have he := hpi.symm e
  have hfm : Measurable (fun x => f (TwoBlockUnipotentQuotient.blockUnipotentEquiv h F
      (e.symm x))) := hf.comp (hm.comp e.symm.measurable)
  have hfe : Measurable (fun x => f (TwoBlockUnipotentQuotient.blockUnipotentEquiv h F x)) :=
    hf.comp hm
  rw [← he.lintegral_comp hfe, lintegral_prod _ hfm.aemeasurable]

end Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient
