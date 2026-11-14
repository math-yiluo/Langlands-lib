import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockQuotientTower
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockFiberKernel
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockQuotientUnfolding
noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient
open Langlands.RankinSelberg.TwoBlockFirstBlockQuotient hiding MixedQuotient NormOneRightInvariant NormalizedTowerStatement blockUnipotent_le_mixedSubgroup continuous_determinantOrder continuous_fiberPoint determinantOrder determinantOrder_mk determinantSlice determinant_mixedEmbedding fiberIntegral fiberIntegral_def fiberIntegral_mixedEmbedding_mul fiberIntegral_mixedSubgroup_mul fiberKernel fiberKernel_mk fiberKernel_zero_comp fiberKernel_zero_comp_restrict fiberMeasures_mixedSubgroup_mul fiberPoint_mem_determinantSlice_iff fiberPoint_mixedEmbedding_mul firstBlockAverage firstBlockAverage_mk instBorelSpaceBlockQuotientCarrier instBorelSpaceGeneralLinearCarrier instBorelSpaceGeneralLinearCarrier_1 instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceMixedQuotient instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instLocallyCompactSpaceGeneralLinearCarrier instLocallyCompactSpaceMatrixFinCarrier instLocallyCompactSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instLocallyCompactSpaceSubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceBlockQuotientCarrier instMeasurableSpaceGeneralLinearCarrier instMeasurableSpaceGeneralLinearCarrier_1 instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceMixedQuotient instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instSecondCountableTopologyGeneralLinearCarrier instSecondCountableTopologyGeneralLinearCarrier_1 instSecondCountableTopologySubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instSecondCountableTopologySubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instT2SpaceCarrier instT2SpaceCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 isClopen_determinantSlice isClosed_mixedSubgroup isOpenEmbedding_normOneSubtype lintegral_blockHaar lintegral_comp_quotientAverageReal lintegral_fiberPoint_quotientAverageReal map_normOneHaar map_restrict_smallSlice measurableSet_determinantSlice measurable_fiberMeasures mem_determinantSlice mem_mixedSubgroup_iff mem_mixedSubgroup_iff_determinantNorm mem_normOneSubgroup_iff mem_normOneSubgroup_iff_normalizedAbs mixedCoordinates mixedCoordinates_mixedEmbedding mixedEmbedding mixedEmbedding_apply mixedEmbedding_index_one_one mixedEmbedding_index_one_zero mixedEmbedding_index_zero_one mixedEmbedding_index_zero_zero mixedEmbedding_mem mixedEmbedding_mixedCoordinates mixedHaar mixedHaar_isHaar mixedHaar_isMulRightInvariant mixedHaar_regular mixedSubgroup mixedSubgroupEquiv mixedSubgroupEquiv_apply_val mixedSubgroupHomeomorph mixedSubgroup_le_normOneSubgroup mixedSubgroup_le_parabolic mixed_compatibleMeasureExists normOneHaar normOneHaar_isHaar normOneHaar_isMulRightInvariant normOneHaar_regular normOneRightInvariant_of_isCompatible normOneSubgroup normalized_tower ord_determinant_eq_zero small_orbitKernel_comp_zero towerBlockQuotientLocallyCompact towerBlockQuotientSecondCountable towerBlockQuotientT2 towerInst1 towerInst10 towerInst11 towerInst12 towerInst13 towerInst14 towerInst15 towerInst16 towerInst17 towerInst2 towerInst20 towerInst21 towerInst23 towerInst24 towerInst25 towerInst26 towerInst27 towerInst28 towerInst29 towerInst3 towerInst30 towerInst4 towerInst8 towerInst9 unfoldingInst1 unfoldingInst10 unfoldingInst11 unfoldingInst12 unfoldingInst13 unfoldingInst14 unfoldingInst15 unfoldingInst2 unfoldingInst20 unfoldingInst21 unfoldingInst23 unfoldingInst24 unfoldingInst3 unfoldingInst4 unfoldingInst8 unfoldingInst9
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

local instance towerInst4 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance towerInst8 (n : ℕ) : MeasurableSpace (GeneralLinear n F) := borel _
local instance towerInst9 (n : ℕ) : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
local instance towerInst10 (n : ℕ) : SecondCountableTopology (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology n
local instance towerInst11 (n : ℕ) : LocallyCompactSpace (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace n
local instance towerInst12 (n : ℕ) : MeasurableSpace (upperUnipotent n F) := borel _
local instance towerInst13 (n : ℕ) : BorelSpace (upperUnipotent n F) := ⟨rfl⟩
local instance towerInst14 (n : ℕ) : SecondCountableTopology (upperUnipotent n F) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance towerInst15 (n : ℕ) : LocallyCompactSpace (upperUnipotent n F) :=
  UpperUnipotent.locallyCompactSpace
local instance towerInst16 (n : ℕ) : MeasurableSpace (normOneSubgroup F n) := borel _
local instance towerInst17 (n : ℕ) : BorelSpace (normOneSubgroup F n) := ⟨rfl⟩
local instance towerInst20 (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n F) := borel _
local instance towerInst21 (n : ℕ) : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
local instance towerInst23 : MeasurableSpace (TwoBlockUnipotentQuotient.blockUnipotent h F) := borel _
local instance towerInst24 : BorelSpace (TwoBlockUnipotentQuotient.blockUnipotent h F) := ⟨rfl⟩
local instance towerInst25 : MeasurableSpace (TwoBlockUnipotentQuotient.BlockQuotient h F) := borel _
local instance towerInst26 : BorelSpace (TwoBlockUnipotentQuotient.BlockQuotient h F) := ⟨rfl⟩
local instance towerInst27 : MeasurableSpace (mixedSubgroup F h) := borel _
local instance towerInst28 : BorelSpace (mixedSubgroup F h) := ⟨rfl⟩
local instance towerInst29 : MeasurableSpace (MixedQuotient F h) := borel _
local instance towerInst30 : BorelSpace (MixedQuotient F h) := ⟨rfl⟩

/-- Integrating the block average over the small zero slice gives the exact mixed average. -/
theorem lintegral_fiberPoint_quotientAverageReal
    (νA : Measure (LeftUnipotentQuotient (m 0) F))
    (hνA : IsCompatible (upperUnipotent (m 0 + 1) F)
      (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) νA)
    (f : C_c(GeneralLinear (t + 1) F, ℝ)) (hf0 : ∀ x, 0 ≤ f x)
    (g : GeneralLinear (t + 1) F) :
    ∫⁻ q, ENNReal.ofReal (quotientAverageReal
        (TwoBlockUnipotentQuotient.blockUnipotent h F)
        (TwoBlockUnipotentQuotient.blockHaar F h) f (fiberPoint h F q g))
      ∂νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) 0) =
      ENNReal.ofReal (quotientAverageReal (mixedSubgroup F h) (mixedHaar F h) f
        (Quotient.mk _ g)) := by
  let D : GeneralLinear (m 0 + 1) F × upperUnipotent (m 1 + 1) F →
      GeneralLinear (t + 1) F :=
    fun x => (succBlockShape m h).leviEmbedding F (blockPair F (x.1, x.2.val))
  have hDc : Continuous D :=
    ((succBlockShape m h).leviEmbeddingContinuous F).continuous.comp
      ((continuous_blockPair F).comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  let Φ : GeneralLinear (m 0 + 1) F → ℝ≥0∞ :=
    fun u => ∫⁻ b : upperUnipotent (m 1 + 1) F,
      ENNReal.ofReal (f (D (u, b) * g)) ∂unipotentHaar F (m 1)
  have hΦ : Measurable Φ :=
    (ENNReal.continuous_ofReal.comp (f.continuous.comp (hDc.mul_const g))).measurable.lintegral_prod_right'
  have hblock (a : upperUnipotent (m 0 + 1) F)
      (b : upperUnipotent (m 1 + 1) F) (u : GeneralLinear (m 0 + 1) F) :
      (TwoBlockUnipotentQuotient.blockUnipotentEquiv h F
        ((MeasurableEquiv.piFinTwo _).symm (a, b))).val * firstBlockEmbedding h F u =
          D (a.val * u, b) := by
    rw [TwoBlockUnipotentQuotient.blockUnipotentEquiv_apply_val,
      TwoBlockUnipotentQuotient.blockEmbedding_apply, firstBlockEmbedding_apply, ← map_mul]
    congr 1
    funext i
    fin_cases i <;> simp [MeasurableEquiv.piFinTwo, piFinTwoEquiv]
  have hrep (u : GeneralLinear (m 0 + 1) F) :
      ENNReal.ofReal (quotientAverageReal
        (TwoBlockUnipotentQuotient.blockUnipotent h F)
        (TwoBlockUnipotentQuotient.blockHaar F h) f
        (fiberPoint h F (Quotient.mk _ u) g)) =
      ∫⁻ a : upperUnipotent (m 0 + 1) F,
        Φ (a.val * u) ∂unipotentHaar F (m 0) := by
    rw [fiberPoint_mk, quotientAverageReal_mk,
      ofReal_integral_eq_lintegral_ofReal
        (integrable_subgroup_mul _ (TwoBlockUnipotentQuotient.isClosed_blockUnipotent h F)
          (TwoBlockUnipotentQuotient.blockHaar F h) f _)
        (Filter.Eventually.of_forall fun _ => hf0 _)]
    have hfm : Measurable (fun b : TwoBlockUnipotentQuotient.blockUnipotent h F =>
        ENNReal.ofReal (f (b.val * (firstBlockEmbedding h F u * g)))) :=
      (ENNReal.continuous_ofReal.comp
        (f.continuous.comp (continuous_subtype_val.mul_const _))).measurable
    rw [lintegral_blockHaar F h _ hfm]
    apply lintegral_congr
    intro a
    apply lintegral_congr
    intro b
    rw [← mul_assoc, hblock]
  let κA := orbitKernel (upperUnipotent (m 0 + 1) F)
    (UpperUnipotent.isClosed (R := F)) (unipotentHaar F (m 0))
  have hmix : Measurable (mixedSubgroupEquiv F h) :=
    (mixedSubgroupHomeomorph F h).continuous.measurable
  have hmfm : Measurable (fun l : mixedSubgroup F h => ENNReal.ofReal (f (l.val * g))) :=
    (ENNReal.continuous_ofReal.comp
      (f.continuous.comp (continuous_subtype_val.mul_const g))).measurable
  have hmixrep : ENNReal.ofReal (quotientAverageReal (mixedSubgroup F h) (mixedHaar F h) f
      (Quotient.mk _ g)) = ∫⁻ u : normOneSubgroup F (m 0 + 1), Φ u.val ∂normOneHaar F (m 0) := by
    rw [quotientAverageReal_mk, ofReal_integral_eq_lintegral_ofReal
      (integrable_subgroup_mul _ (isClosed_mixedSubgroup F h) (mixedHaar F h) f g)
      (Filter.Eventually.of_forall fun _ => hf0 _), mixedHaar, lintegral_map hmfm hmix]
    have hprod : Measurable (fun x : normOneSubgroup F (m 0 + 1) ×
        upperUnipotent (m 1 + 1) F =>
        ENNReal.ofReal (f ((mixedSubgroupEquiv F h x).val * g))) := hmfm.comp hmix
    rw [lintegral_prod _ hprod.aemeasurable]
    rfl
  calc
    _ = ∫⁻ q, ∫⁻ v, Φ v ∂κA q ∂νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) 0) := by
      apply lintegral_congr
      intro q
      induction q using Quotient.inductionOn with
      | h u =>
        rw [hrep, show κA (Quotient.mk _ u) = _ from orbitKernel_mk _ _ _ u,
          lintegral_map hΦ (continuous_subtype_val.mul_const u).measurable]
    _ = ∫⁻ v, Φ v ∂(κA ∘ₘ νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) 0)) :=
      (Measure.lintegral_bind κA.measurable.aemeasurable hΦ.aemeasurable).symm
    _ = ∫⁻ v, Φ v ∂Measure.map Subtype.val (normOneHaar F (m 0)) := by
      rw [show κA ∘ₘ νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) 0) = _ from
        small_orbitKernel_comp_zero F (m 0) νA hνA]
    _ = _ := by rw [lintegral_map hΦ continuous_subtype_val.measurable, hmixrep]

local instance towerBlockQuotientT2 :
    T2Space (TwoBlockUnipotentQuotient.BlockQuotient h F) :=
  leftQuotient_t2Space _ (TwoBlockUnipotentQuotient.isClosed_blockUnipotent h F)
local instance towerBlockQuotientLocallyCompact :
    LocallyCompactSpace (TwoBlockUnipotentQuotient.BlockQuotient h F) :=
  leftQuotient_locallyCompactSpace _
local instance towerBlockQuotientSecondCountable :
    SecondCountableTopology (TwoBlockUnipotentQuotient.BlockQuotient h F) :=
  Topology.IsOpenQuotientMap.secondCountableTopology (leftQuotient_isOpenQuotientMap _)

/-- The composite zero-slice fiber measure integrates block averages to mixed averages. -/
theorem lintegral_comp_quotientAverageReal
    (νA : Measure (LeftUnipotentQuotient (m 0) F)) [SFinite νA]
    (hInv : NormOneRightInvariant F (m 0) νA)
    (hνA : IsCompatible (upperUnipotent (m 0 + 1) F)
      (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) νA)
    (νL : Measure (MixedQuotient F h))
    (f : C_c(GeneralLinear (t + 1) F, ℝ)) (hf0 : ∀ x, 0 ≤ f x) :
    ∫⁻ z, ENNReal.ofReal (quotientAverageReal
        (TwoBlockUnipotentQuotient.blockUnipotent h F)
        (TwoBlockUnipotentQuotient.blockHaar F h) f z)
      ∂(fiberKernel F h νA hInv 0 ∘ₘ νL) =
      ∫⁻ q, ENNReal.ofReal (quotientAverageReal (mixedSubgroup F h) (mixedHaar F h) f q) ∂νL := by
  have hHm : Measurable (fun z => ENNReal.ofReal (quotientAverageReal
      (TwoBlockUnipotentQuotient.blockUnipotent h F)
      (TwoBlockUnipotentQuotient.blockHaar F h) f z)) :=
    (ENNReal.continuous_ofReal.comp (continuous_quotientAverageReal _
      (TwoBlockUnipotentQuotient.isClosed_blockUnipotent h F) _ f)).measurable
  rw [Measure.lintegral_bind (fiberKernel F h νA hInv 0).measurable.aemeasurable hHm.aemeasurable]
  apply lintegral_congr
  intro q
  induction q using Quotient.inductionOn with
  | h g =>
    have hfm : Measurable (fun a => fiberPoint h F a g) :=
      ((continuous_fiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
    rw [fiberKernel_mk, lintegral_map hHm hfm]
    exact lintegral_fiberPoint_quotientAverageReal F h νA hνA f hf0 g

/-- The normalized full tower has coefficient exactly one. -/
theorem fiberKernel_zero_comp
    (νA : Measure (LeftUnipotentQuotient (m 0) F)) [SFinite νA]
    (hInv : NormOneRightInvariant F (m 0) νA)
    (hνA : IsCompatible (upperUnipotent (m 0 + 1) F)
      (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) νA)
    (νL : Measure (MixedQuotient F h))
    (hνL : IsCompatible (mixedSubgroup F h) (generalLinearHaar F t) (mixedHaar F h) νL)
    (νH : Measure (TwoBlockUnipotentQuotient.BlockQuotient h F))
    (hνH : IsCompatible (TwoBlockUnipotentQuotient.blockUnipotent h F)
      (generalLinearHaar F t) (TwoBlockUnipotentQuotient.blockHaar F h) νH) :
    fiberKernel F h νA hInv 0 ∘ₘ νL = νH := by
  let H := TwoBlockUnipotentQuotient.blockUnipotent h F
  let μH := TwoBlockUnipotentQuotient.blockHaar F h
  let μG := generalLinearHaar F t
  let κ := fiberKernel F h νA hInv 0
  have hH := TwoBlockUnipotentQuotient.isClosed_blockUnipotent h F
  have hL : ∀ f : C_c(GeneralLinear (t + 1) F, ℝ), (∀ y, 0 ≤ f y) →
      ∫⁻ z, ENNReal.ofReal (quotientAverageReal H μH f z) ∂(κ ∘ₘ νL) =
        ∫⁻ y, ENNReal.ofReal (f y) ∂μG := by
    intro f hf0
    rw [lintegral_comp_quotientAverageReal F h νA hInv hνA νL f hf0,
      RecursiveIntegration.lintegral_quotientAverageReal _ _ _ _ hνL
        f f.continuous f.hasCompactSupport hf0]
  have hR : ∀ f : C_c(GeneralLinear (t + 1) F, ℝ), (∀ y, 0 ≤ f y) →
      ∫⁻ z, ENNReal.ofReal (quotientAverageReal H μH f z) ∂νH =
        ∫⁻ y, ENNReal.ofReal (f y) ∂μG := by
    intro f hf0
    exact RecursiveIntegration.lintegral_quotientAverageReal H μG μH νH hνH
      f f.continuous f.hasCompactSupport hf0
  have hlift : ∀ φ : C_c(TwoBlockUnipotentQuotient.BlockQuotient h F, ℝ),
      (∀ q, 0 ≤ φ q) → ∃ f : C_c(GeneralLinear (t + 1) F, ℝ),
        (∀ y, 0 ≤ f y) ∧ ∀ q, quotientAverageReal H μH f q = φ q := by
    intro φ hφ
    obtain ⟨f, hf, hf0⟩ := realQuotientPositiveLifting H hH μH φ
    refine ⟨f, hf0 hφ, fun q => ?_⟩
    induction q using Quotient.inductionOn with
    | h g => exact hf g
  have hfin : IsFiniteMeasureOnCompacts (κ ∘ₘ νL) := by
    refine ⟨fun C hC => ?_⟩
    obtain ⟨u, hu1, -, hucs, hu01⟩ :=
      exists_continuous_one_zero_of_isCompact hC isClosed_empty (Set.disjoint_empty C)
    let φ : C_c(TwoBlockUnipotentQuotient.BlockQuotient h F, ℝ) := ⟨u, hucs⟩
    obtain ⟨f, hf0, hfavg⟩ := hlift φ fun q => (hu01 q).1
    calc (κ ∘ₘ νL) C = ∫⁻ q, C.indicator 1 q ∂(κ ∘ₘ νL) :=
        (lintegral_indicator_one hC.isClosed.measurableSet).symm
      _ ≤ ∫⁻ q, ENNReal.ofReal (quotientAverageReal H μH f q) ∂(κ ∘ₘ νL) := by
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
      _ = ∫⁻ y, ENNReal.ofReal (f y) ∂μG := hL f hf0
      _ < ⊤ := (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport).lintegral_lt_top
  have : (κ ∘ₘ νL).Regular := inferInstance
  have : νH.Regular := hνH.regular
  apply Measure.ext_of_integral_eq_on_compactlySupported_nnreal
  intro φ
  let φr : C_c(TwoBlockUnipotentQuotient.BlockQuotient h F, ℝ) :=
    ⟨⟨fun q => (φ q : ℝ), NNReal.continuous_coe.comp φ.continuous⟩,
      φ.hasCompactSupport.comp_left NNReal.coe_zero⟩
  obtain ⟨f, hf0, hfavg⟩ := hlift φr fun q => (φ q).coe_nonneg
  have key : ∀ μ' : Measure (TwoBlockUnipotentQuotient.BlockQuotient h F),
      ∫⁻ q, ENNReal.ofReal (quotientAverageReal H μH f q) ∂μ' =
        ∫⁻ y, ENNReal.ofReal (f y) ∂μG →
      ∫ q, (φ q : ℝ) ∂μ' = (∫⁻ y, ENNReal.ofReal (f y) ∂μG).toReal := by
    intro μ' h'
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun q => (φ q).coe_nonneg)
      (NNReal.continuous_coe.comp φ.continuous).aestronglyMeasurable, ← h']
    congr 1
    apply lintegral_congr
    intro q
    rw [hfavg q]
    rfl
  rw [key _ (hL f hf0), key _ (hR f hf0)]

/-- The zero small slice preserves the determinant slice of the mixed base. -/
theorem fiberKernel_zero_comp_restrict
    (νA : Measure (LeftUnipotentQuotient (m 0) F)) [SFinite νA]
    (hInv : NormOneRightInvariant F (m 0) νA)
    (νL : Measure (MixedQuotient F h))
    (νH : Measure (TwoBlockUnipotentQuotient.BlockQuotient h F))
    (hcomp : fiberKernel F h νA hInv 0 ∘ₘ νL = νH) (k : ℤ) :
    fiberKernel F h νA hInv 0 ∘ₘ νL.restrict (determinantSlice F h k) =
      νH.restrict (Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.determinantSlice F h k) := by
  let κ := fiberKernel F h νA hInv 0
  let sA := Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) 0
  let sL := determinantSlice F h k
  let sH := Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.determinantSlice F h k
  have hsL : MeasurableSet sL := measurableSet_determinantSlice F h k
  have hsH : MeasurableSet sH := Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.measurableSet_determinantSlice F h k
  have hpt : ∀ A, MeasurableSet A → ∀ q,
      κ q (A ∩ sH) = sL.indicator (fun q => κ q A) q := by
    intro A hA q
    induction q using Quotient.inductionOn with
    | h g =>
      have hfm : Measurable (fun a => fiberPoint h F a g) :=
        ((continuous_fiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
      have hsupport : ∀ a, a ∈ sA →
          (fiberPoint h F a g ∈ sH ↔ (Quotient.mk _ g : MixedQuotient F h) ∈ sL) := by
        intro a ha
        change Langlands.AllField.RankinSelberg.determinantOrder (⟨⟩ : LocalFieldData F) (m 0) a = 0 at ha
        rw [show (fiberPoint h F a g ∈ sH) ↔ _ from
          fiberPoint_mem_determinantSlice_iff F h a g k, ha, zero_add]
        rfl
      rw [show κ (Quotient.mk _ g) = _ from fiberKernel_mk F h νA hInv 0 g,
        Measure.map_apply hfm (hA.inter hsH), Measure.restrict_apply (hfm (hA.inter hsH))]
      by_cases hg : (Quotient.mk _ g : MixedQuotient F h) ∈ sL
      · rw [Set.indicator_of_mem hg,
          show κ (Quotient.mk _ g) = _ from fiberKernel_mk F h νA hInv 0 g,
          Measure.map_apply hfm hA, Measure.restrict_apply (hfm hA)]
        congr 1
        ext a
        change ((fiberPoint h F a g ∈ A ∧ fiberPoint h F a g ∈ sH) ∧ a ∈ sA) ↔
          (fiberPoint h F a g ∈ A ∧ a ∈ sA)
        exact ⟨fun ha => ⟨ha.1.1, ha.2⟩, fun ha => ⟨⟨ha.1, (hsupport a ha.2).2 hg⟩, ha.2⟩⟩
      · rw [Set.indicator_of_notMem hg]
        have he : ((fun a => fiberPoint h F a g) ⁻¹' (A ∩ sH)) ∩ sA = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro a ha
          exact hg ((hsupport a ha.2).1 ha.1.2)
        rw [show Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) 0 = sA from rfl,
          he, measure_empty]
  ext A hA
  change (κ ∘ₘ νL.restrict sL) A = νH.restrict sH A
  rw [Measure.bind_apply hA κ.measurable.aemeasurable, Measure.restrict_apply hA,
    ← lintegral_indicator hsL]
  rw [show (∫⁻ q, sL.indicator (fun q => κ q A) q ∂νL) =
      ∫⁻ q, κ q (A ∩ sH) ∂νL from lintegral_congr fun q => (hpt A hA q).symm]
  rw [← Measure.bind_apply (hA.inter hsH) κ.measurable.aemeasurable, hcomp]

/-- Exact full and same-slice composition for the zero small-slice kernel. -/
abbrev NormalizedTowerStatement
    (νA : Measure (LeftUnipotentQuotient (m 0) F)) [SFinite νA]
    (hInv : NormOneRightInvariant F (m 0) νA)
    (νL : Measure (MixedQuotient F h))
    (νH : Measure (TwoBlockUnipotentQuotient.BlockQuotient h F)) : Prop :=
  (fiberKernel F h νA hInv 0 ∘ₘ νL = νH) ∧
    ∀ k : ℤ, fiberKernel F h νA hInv 0 ∘ₘ νL.restrict (determinantSlice F h k) =
      νH.restrict (Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.determinantSlice F h k)

/-- Compatible measures satisfy the normalized full tower and all its same-slice restrictions. -/
theorem normalized_tower
    (νA : Measure (LeftUnipotentQuotient (m 0) F)) [SFinite νA]
    (hInv : NormOneRightInvariant F (m 0) νA)
    (hνA : IsCompatible (upperUnipotent (m 0 + 1) F)
      (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) νA)
    (νL : Measure (MixedQuotient F h))
    (hνL : IsCompatible (mixedSubgroup F h) (generalLinearHaar F t) (mixedHaar F h) νL)
    (νH : Measure (TwoBlockUnipotentQuotient.BlockQuotient h F))
    (hνH : IsCompatible (TwoBlockUnipotentQuotient.blockUnipotent h F)
      (generalLinearHaar F t) (TwoBlockUnipotentQuotient.blockHaar F h) νH) :
    NormalizedTowerStatement F h νA hInv νL νH := by
  have hc := fiberKernel_zero_comp F h νA hInv hνA νL hνL νH hνH
  exact ⟨hc, fiberKernel_zero_comp_restrict F h νA hInv νL νH hc⟩

end Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient
