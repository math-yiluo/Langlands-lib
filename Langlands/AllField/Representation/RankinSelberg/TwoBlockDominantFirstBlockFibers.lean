import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockFibers
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantFirstBlockQuotient
/-! # Actual product fibers in the first-block disintegration -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg.TwoBlockDominantFirstBlock hiding UpperSliceConverges continuous_diagonalIntegrand continuous_upperAverage diagonalSupportGLTopological diagonalSupportT2 diagonalSupportTopology diagonalWhittaker_slice_hasCompactSupport exists_rectangularSectionExpansion exists_uniformOrdinaryJacquetRealization firstFiberBorel firstFiberCountable firstFiberGLBorel firstFiberGLCountable firstFiberGLMeasurable firstFiberGLTopology firstFiberHBorel firstFiberHMeasurable firstFiberHQBorel firstFiberHQMeasurable firstFiberLocalField firstFiberMeasurable firstFiberMixedMeasurable firstFiberMixedSubgroupBorel firstFiberMixedSubgroupMeasurable firstFiberNBorel firstFiberNCountable firstFiberNMeasurable firstFiberNQBorel firstFiberNQMeasurable firstFiberT2 firstFiberTopology firstFiberValuation firstQuotientCountable firstQuotientGLBorel firstQuotientGLCountable firstQuotientGLMeasurable firstQuotientGLTopology firstQuotientHBorel firstQuotientHMeasurable firstQuotientHQBorel firstQuotientHQMeasurable firstQuotientLocalField firstQuotientMeasurable firstQuotientMixedMeasurable firstQuotientMixedSubgroupBorel firstQuotientMixedSubgroupMeasurable firstQuotientNBorel firstQuotientNCountable firstQuotientNMeasurable firstQuotientNQMeasurable firstQuotientT2 firstQuotientTopology firstQuotientValuation instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instIsNonarchimedeanLocalFieldCarrier instIsTopologicalGroupGeneralLinearCarrier instLocallyCompactSpaceGeneralLinearCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instSecondCountableTopologyCarrier instSecondCountableTopologyGeneralLinearCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instValuativeRelCarrier integrable_rectangularBorelMeasure rectangleUnfoldingCountable rectangleUnfoldingGLBorel rectangleUnfoldingGLCountable rectangleUnfoldingGLMeasurable rectangleUnfoldingGLTopology rectangleUnfoldingHBorel rectangleUnfoldingHMeasurable rectangleUnfoldingHQMeasurable rectangleUnfoldingLocalField rectangleUnfoldingMeasurable rectangleUnfoldingNBorel rectangleUnfoldingNCountable rectangleUnfoldingNMeasurable rectangleUnfoldingNQMeasurable rectangleUnfoldingT2 rectangleUnfoldingTopology rectangleUnfoldingValuation rectangularBorelMeasure rectangularSectionAverage rectangularSectionAverage_firstBlock_unfolding rectangularSectionIntegrand rectangularSectionIntegrand_expansion rectangularSectionIntegrand_integrable rectangularSectionIntegrand_mk rectangularSectionIntegrand_regular rectangularSectionNormProfile rectangularSection_firstBlock_product_fibers rectangularWhittaker rectangularWhittaker_apply sectionAverage_mk sectionAverages_continuous sectionIntegrand sectionIntegrand_continuous sectionIntegrand_fiberPoint sectionIntegrand_mk sectionIntegrand_slice_unfolding sectionNormAverage_mk sectionUnfoldingBorel sectionUnfoldingCountable sectionUnfoldingGLBorel sectionUnfoldingGLCountable sectionUnfoldingGLLocalCompact sectionUnfoldingGLMeasurable sectionUnfoldingGLTopology sectionUnfoldingHBorel sectionUnfoldingHMeasurable sectionUnfoldingHQBorel sectionUnfoldingHQMeasurable sectionUnfoldingLocalField sectionUnfoldingMeasurable sectionUnfoldingNBorel sectionUnfoldingNCountable sectionUnfoldingNMeasurable sectionUnfoldingNQBorel sectionUnfoldingNQMeasurable sectionUnfoldingT2 sectionUnfoldingTopology sectionUnfoldingValuation upperSliceConverges
open Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankLastRowReductionStatement EqualRankNormalizedCompactIntegrationStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement SliceIntegrable SliceIntegrableAt TwoBlockFirstBlockQuotientIntegrationStatement TwoBlockJacquetConvergenceStatement TwoBlockOrdinaryJacquetFunctionalStatement TwoBlockUnipotentQuotientIntegrationStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankLastRowReduction equalRankNormalizedCompactIntegration equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound finiteFunctionMellin finiteFunctionShellSeries hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductWhittakerType oneVariableMellin pairwise_disjoint_determinantSlice quotientIwasawaIntegration quotientRootIntegration rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight setIntegral_equalRankIntegrand_determinantSlice setIntegral_unequalRankAverage_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrableAt_unequalRankAverage_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockFirstBlockQuotientIntegration twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val twoBlockOrdinaryJacquetFunctional twoBlockUnipotentQuotientIntegration unequalRankAnalytic unequalRankAverage unequalRankAverage_eq_mul_spectralPoint_zpow unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankIwasawaSupport unequalRankSliceCoefficient unequalRankSliceExpansion unequalRankSliceExpansion_of_converges unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unequalSliceMatrixMeasurable unequalSliceQuotientBorel unequalSliceQuotientMeasurable unequalSliceTopology whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory ProbabilityTheory
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.Whittaker hiding CompactLocalizationStatement MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier UnipotentOrbitStatement compactLocalization exchangedParabolic functionalsCongr hasCompactSupport_twoBlockCellRestriction inducedLocalization_of_prerequisites mirabolicUnitTest modelKirillovTransfer mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentOrbit unipotentShift
open Langlands.AllField.Whittaker
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockUnipotentQuotient hiding FiberKernelSFiniteStatement analytic_of_comp_eq_smul continuous_fiberPoint continuous_projection determinantSlice fiberIntegral fiberIntegral_def fiberIntegral_upperUnipotent_mul fiberKernel fiberKernel_compact_ne_top fiberKernel_isSFinite fiberKernel_mk fiberMeasures_upperUnipotent_mul iUnion_determinantSlice integerCube_mass_pos_lt_top isClopen_determinantSlice map_unipotentShift measurableSet_determinantSlice measurable_fiberMeasures mem_determinantSlice mk_mem_determinantSlice pairwise_disjoint_determinantSlice radicalAverage radicalAverage_eq_integral_kernel radicalAverage_mk
open Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient hiding determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open scoped ENNReal

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance firstFiberT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance firstFiberCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance firstFiberGLTopology (a : ℕ) :
    IsTopologicalGroup (GeneralLinear a F) :=
  (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup a
local instance firstFiberGLLocalCompact (a : ℕ) :
    LocallyCompactSpace (GeneralLinear a F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace a
local instance firstFiberGLCountable (a : ℕ) :
    SecondCountableTopology (GeneralLinear a F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology a
local instance firstFiberMeasurable : MeasurableSpace F := borel _
local instance firstFiberBorel : BorelSpace F := ⟨rfl⟩
local instance firstFiberGLMeasurable (a : ℕ) :
    MeasurableSpace (GeneralLinear a F) := borel _
local instance firstFiberGLBorel (a : ℕ) :
    BorelSpace (GeneralLinear a F) := ⟨rfl⟩
local instance firstFiberNMeasurable (a : ℕ) :
    MeasurableSpace (upperUnipotent a F) := borel _
local instance firstFiberNBorel (a : ℕ) :
    BorelSpace (upperUnipotent a F) := ⟨rfl⟩
local instance firstFiberNCountable (a : ℕ) :
    SecondCountableTopology (upperUnipotent a F) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance firstFiberNQMeasurable (a : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient a F) := borel _
local instance firstFiberNQBorel (a : ℕ) :
    BorelSpace (LeftUnipotentQuotient a F) := ⟨rfl⟩

variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}
  {ψ : UnitaryAdditiveCharacter F}

local instance firstFiberHMeasurable :
    MeasurableSpace (blockUnipotent h F) := borel _
local instance firstFiberHBorel :
    BorelSpace (blockUnipotent h F) := ⟨rfl⟩
local instance firstFiberHQMeasurable :
    MeasurableSpace (BlockQuotient h F) := borel _
local instance firstFiberHQBorel :
    BorelSpace (BlockQuotient h F) := ⟨rfl⟩

local instance firstFiberMixedSubgroupMeasurable :
    MeasurableSpace (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedSubgroup F h) := borel _
local instance firstFiberMixedSubgroupBorel :
    BorelSpace (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedSubgroup F h) := ⟨rfl⟩
local instance firstFiberMixedMeasurable :
    MeasurableSpace (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.MixedQuotient F h) := borel _
local instance firstFiberMixedBorel :
    BorelSpace (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.MixedQuotient F h) := ⟨rfl⟩

variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
  (f : Sections F h σ)

/-- The real integral of the raw rectangle norm on the block quotient. -/
def rectangularSectionNormProfile (j k : ℕ)
    (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))
    (ν : AdditiveHaarMeasure F)
    (weight : LeftUnipotentQuotient t F → ℂ)
    (z : BlockQuotient h F) : ℝ :=
  ∫ x, ‖rectangularSectionIntegrand F ell f j k Wtest weight x z‖
    ∂rectangularMeasure ν j (t + 1)

/-- Disintegrate the real raw-norm profile before invoking Fubini on the
actual first-block quotient times the actual external rectangle. -/
theorem rectangularSection_firstBlock_product_fibers (j k : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (t + (j + k + 1) + 1) F) V)
    (hπ : IsOfWhittakerType (t + (j + k + 1))
      (standardCharacter ψ (t + (j + k + 1))) π)
    (lambda : glFunctionals ψ (t + (j + k + 1)) π)
    (Wtest : (coefficientModel π lambda).toSubmodule)
    (weight : LeftUnipotentQuotient t F → ℂ) (hw : Continuous weight)
    (μR : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
    [μR.IsAddHaarMeasure] (hraw : IsAbsIntegrable ψ (fun i => (ell i).val) μR f)
    (ν : AdditiveHaarMeasure F)
    (νN : Measure (LeftUnipotentQuotient t F))
    (νH : Measure (BlockQuotient h F)) [SigmaFinite νH]
    (νA : Measure (LeftUnipotentQuotient (m 0) F)) [SigmaFinite νA]
    (νM : Measure (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.MixedQuotient F h))
    (hνN : IsCompatible (upperUnipotent (t + 1) F)
      (generalLinearHaar F t) (unipotentHaar F t) νN)
    (hνH : IsCompatible (blockUnipotent h F)
      (generalLinearHaar F t) (blockHaar F h) νH)
    (hνA : IsCompatible (upperUnipotent (m 0 + 1) F)
      (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) νA)
    (hνM : IsCompatible (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedSubgroup F h)
      (generalLinearHaar F t) (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedHaar F h) νM)
    (a : ℤ) :
    let hInv := Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.normOneRightInvariant_of_isCompatible F (m 0)
      (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) νA hνA
    let κ := Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.fiberKernel F h νA hInv a
    let N := rectangularSectionNormProfile F ell f j k Wtest.val ν weight
    let P := fun q => ∫ z, N z ∂κ q
    let μM := νM.restrict (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.determinantSlice F h 0)
    Measurable N ∧
    Integrable N (νH.restrict (Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.determinantSlice F h a)) ∧
    Measurable P ∧ Integrable P μM ∧
    (∀ q (g : GeneralLinear (t + 1) F), q = Quotient.mk _ g →
      P q = ∫ v in Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) a,
        ∫ x, ‖rectangularSectionIntegrand F ell f j k Wtest.val weight x
          (TwoBlockFirstBlockQuotient.fiberPoint h F v g)‖
          ∂rectangularMeasure ν j (t + 1) ∂νA) ∧
    ∀ᵐ q ∂μM, ∀ g : GeneralLinear (t + 1) F, q = Quotient.mk _ g →
      Integrable (fun z : LeftUnipotentQuotient (m 0) F ×
          Matrix (Fin j) (Fin (t + 1)) F =>
        rectangularSectionIntegrand F ell f j k Wtest.val weight z.2
          (TwoBlockFirstBlockQuotient.fiberPoint h F z.1 g))
        ((νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F)
          (m 0) a)).prod (rectangularMeasure ν j (t + 1))) ∧
      Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.firstBlockAverage F h νA hInv a
        (rectangularSectionAverage F ell f j k Wtest.val ν weight) q =
        ∫ x, ∫ v in Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) a,
          rectangularSectionIntegrand F ell f j k Wtest.val weight x
            (TwoBlockFirstBlockQuotient.fiberPoint h F v g) ∂νA
              ∂rectangularMeasure ν j (t + 1) := by
  dsimp only
  let hInv := Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.normOneRightInvariant_of_isCompatible F (m 0)
    (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) νA hνA
  let κ := Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.fiberKernel F h νA hInv a
  let μM := νM.restrict (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.determinantSlice F h 0)
  let μA := νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) a)
  let E := fun z : BlockQuotient h F ×
      Matrix (Fin j) (Fin (t + 1)) F =>
    rectangularSectionIntegrand F ell f j k Wtest.val weight z.2 z.1
  let N := rectangularSectionNormProfile F ell f j k Wtest.val ν weight
  have hreg := rectangularSectionIntegrand_regular F ell f j k π hπ lambda Wtest ν weight hw
  have hEi := rectangularSectionIntegrand_integrable F ell f j k π hπ lambda Wtest
    weight hw μR hraw ν νN νH hνN hνH a
  have hNm : Measurable N := hreg.1.measurable.stronglyMeasurable.norm.integral_prod_right'.measurable
  have hNi : Integrable N
      (νH.restrict (Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.determinantSlice F h a)) :=
    hEi.integral_norm_prod_left
  have hNnonneg (z : BlockQuotient h F) : 0 ≤ N z :=
    integral_nonneg fun _ => norm_nonneg _
  have hzero := (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.normalized_tower F h
    νA hInv hνA νM hνM νH hνH).2
  have hcomp := Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.fiberKernel_comp_zeroSlice_eq F h
    νA hInv hνA νM hνM νH hzero a
  have hNc : Integrable N (κ ∘ₘ μM) := by rw [hcomp]; exact hNi
  obtain ⟨hNae, hPi⟩ := (Measure.integrable_comp_iff hNm.aestronglyMeasurable).mp hNc
  have hPnorm : (fun q => ∫ z, ‖N z‖ ∂κ q) = fun q => ∫ z, N z ∂κ q := by
    funext q
    simp only [Real.norm_eq_abs, abs_of_nonneg (hNnonneg _)]
  rw [hPnorm] at hPi
  refine ⟨hNm, hNi, (hNm.stronglyMeasurable.integral_kernel (κ := κ)).measurable,
    hPi, ?_, ?_⟩
  · intro q g hq
    subst q
    rw [Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.fiberKernel_mk]
    have hfm : Measurable (fun v : LeftUnipotentQuotient (m 0) F =>
        TwoBlockFirstBlockQuotient.fiberPoint h F v g) :=
      ((Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.continuous_fiberPoint F h).comp
        (continuous_id.prodMk continuous_const)).measurable
    exact integral_map hfm.aemeasurable hNm.aestronglyMeasurable
  · filter_upwards [hNae] with q hq g hqg
    subst q
    have hfm : Measurable (fun v : LeftUnipotentQuotient (m 0) F =>
        TwoBlockFirstBlockQuotient.fiberPoint h F v g) :=
      ((Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.continuous_fiberPoint F h).comp
        (continuous_id.prodMk continuous_const)).measurable
    rw [Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.fiberKernel_mk] at hq
    have hNactual := hq.comp_measurable hfm
    have hEm : StronglyMeasurable (fun z : LeftUnipotentQuotient (m 0) F ×
        Matrix (Fin j) (Fin (t + 1)) F =>
        E (TwoBlockFirstBlockQuotient.fiberPoint h F z.1 g, z.2)) :=
      hreg.1.measurable.stronglyMeasurable.comp_measurable
        ((hfm.comp measurable_fst).prodMk measurable_snd)
    have hactual : Integrable (fun z : LeftUnipotentQuotient (m 0) F ×
        Matrix (Fin j) (Fin (t + 1)) F =>
        E (TwoBlockFirstBlockQuotient.fiberPoint h F z.1 g, z.2))
        (μA.prod (rectangularMeasure ν j (t + 1))) := by
      apply (integrable_prod_iff hEm.aestronglyMeasurable).mpr
      constructor
      · exact Filter.Eventually.of_forall fun v =>
          hreg.2.1 (TwoBlockFirstBlockQuotient.fiberPoint h F v g)
      · exact hNactual
    refine ⟨hactual, ?_⟩
    rw [Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.firstBlockAverage_mk]
    exact integral_integral_swap hactual

end Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
