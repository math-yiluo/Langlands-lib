import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockQuotient
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantRectangleUnfolding
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockQuotientIntegrationProof
/-! # First-block disintegration of the actual rectangular section average -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg.TwoBlockDominantFirstBlock hiding UpperSliceConverges continuous_diagonalIntegrand continuous_upperAverage diagonalSupportGLTopological diagonalSupportT2 diagonalSupportTopology diagonalWhittaker_slice_hasCompactSupport exists_rectangularSectionExpansion exists_uniformOrdinaryJacquetRealization firstQuotientCountable firstQuotientGLBorel firstQuotientGLCountable firstQuotientGLMeasurable firstQuotientGLTopology firstQuotientHBorel firstQuotientHMeasurable firstQuotientHQBorel firstQuotientHQMeasurable firstQuotientLocalField firstQuotientMeasurable firstQuotientMixedMeasurable firstQuotientMixedSubgroupBorel firstQuotientMixedSubgroupMeasurable firstQuotientNBorel firstQuotientNCountable firstQuotientNMeasurable firstQuotientNQMeasurable firstQuotientT2 firstQuotientTopology firstQuotientValuation instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instIsNonarchimedeanLocalFieldCarrier instIsTopologicalGroupGeneralLinearCarrier instLocallyCompactSpaceGeneralLinearCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instSecondCountableTopologyCarrier instSecondCountableTopologyGeneralLinearCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instValuativeRelCarrier integrable_rectangularBorelMeasure rectangleUnfoldingCountable rectangleUnfoldingGLBorel rectangleUnfoldingGLCountable rectangleUnfoldingGLMeasurable rectangleUnfoldingGLTopology rectangleUnfoldingHBorel rectangleUnfoldingHMeasurable rectangleUnfoldingHQMeasurable rectangleUnfoldingLocalField rectangleUnfoldingMeasurable rectangleUnfoldingNBorel rectangleUnfoldingNCountable rectangleUnfoldingNMeasurable rectangleUnfoldingNQMeasurable rectangleUnfoldingT2 rectangleUnfoldingTopology rectangleUnfoldingValuation rectangularBorelMeasure rectangularSectionAverage rectangularSectionAverage_firstBlock_unfolding rectangularSectionIntegrand rectangularSectionIntegrand_expansion rectangularSectionIntegrand_integrable rectangularSectionIntegrand_mk rectangularSectionIntegrand_regular rectangularWhittaker rectangularWhittaker_apply sectionAverage_mk sectionAverages_continuous sectionIntegrand sectionIntegrand_continuous sectionIntegrand_fiberPoint sectionIntegrand_mk sectionIntegrand_slice_unfolding sectionNormAverage_mk sectionUnfoldingBorel sectionUnfoldingCountable sectionUnfoldingGLBorel sectionUnfoldingGLCountable sectionUnfoldingGLLocalCompact sectionUnfoldingGLMeasurable sectionUnfoldingGLTopology sectionUnfoldingHBorel sectionUnfoldingHMeasurable sectionUnfoldingHQBorel sectionUnfoldingHQMeasurable sectionUnfoldingLocalField sectionUnfoldingMeasurable sectionUnfoldingNBorel sectionUnfoldingNCountable sectionUnfoldingNMeasurable sectionUnfoldingNQBorel sectionUnfoldingNQMeasurable sectionUnfoldingT2 sectionUnfoldingTopology sectionUnfoldingValuation upperSliceConverges
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

local instance firstQuotientT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance firstQuotientCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance firstQuotientGLTopology (a : ℕ) :
    IsTopologicalGroup (GeneralLinear a F) :=
  (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup a
local instance firstQuotientGLLocalCompact (a : ℕ) :
    LocallyCompactSpace (GeneralLinear a F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace a
local instance firstQuotientGLCountable (a : ℕ) :
    SecondCountableTopology (GeneralLinear a F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology a
local instance firstQuotientMeasurable : MeasurableSpace F := borel _
local instance firstQuotientBorel : BorelSpace F := ⟨rfl⟩
local instance firstQuotientGLMeasurable (a : ℕ) :
    MeasurableSpace (GeneralLinear a F) := borel _
local instance firstQuotientGLBorel (a : ℕ) :
    BorelSpace (GeneralLinear a F) := ⟨rfl⟩
local instance firstQuotientNMeasurable (a : ℕ) :
    MeasurableSpace (upperUnipotent a F) := borel _
local instance firstQuotientNBorel (a : ℕ) :
    BorelSpace (upperUnipotent a F) := ⟨rfl⟩
local instance firstQuotientNCountable (a : ℕ) :
    SecondCountableTopology (upperUnipotent a F) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance firstQuotientNQMeasurable (a : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient a F) := borel _
local instance firstQuotientNQBorel (a : ℕ) :
    BorelSpace (LeftUnipotentQuotient a F) := ⟨rfl⟩

variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}
  {ψ : UnitaryAdditiveCharacter F}

local instance firstQuotientHMeasurable :
    MeasurableSpace (blockUnipotent h F) := borel _
local instance firstQuotientHBorel :
    BorelSpace (blockUnipotent h F) := ⟨rfl⟩
local instance firstQuotientHQMeasurable :
    MeasurableSpace (BlockQuotient h F) := borel _
local instance firstQuotientHQBorel :
    BorelSpace (BlockQuotient h F) := ⟨rfl⟩

local instance firstQuotientMixedSubgroupMeasurable :
    MeasurableSpace (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedSubgroup F h) := borel _
local instance firstQuotientMixedSubgroupBorel :
    BorelSpace (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedSubgroup F h) := ⟨rfl⟩
local instance firstQuotientMixedMeasurable :
    MeasurableSpace (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.MixedQuotient F h) := borel _
local instance firstQuotientMixedBorel :
    BorelSpace (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.MixedQuotient F h) := ⟨rfl⟩

variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
  (f : Sections F h σ)

/-- Integrate the actual external rectangle before using the first-block tower. -/
def rectangularSectionAverage (j k : ℕ)
    (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))
    (ν : AdditiveHaarMeasure F)
    (weight : LeftUnipotentQuotient t F → ℂ)
    (z : BlockQuotient h F) : ℂ :=
  ∫ x, rectangularSectionIntegrand F ell f j k Wtest weight x z
    ∂rectangularMeasure ν j (t + 1)

private theorem firstQuotient_continuous_appendIdentity (n d : ℕ) :
    Continuous (appendIdentity (F := F) n d) := by
  induction d with
  | zero => exact continuous_id
  | succ d ih => exact (GeneralLinear.rankInclusionContinuous 1).continuous.comp ih

/-- Finite coefficient expansion gives joint continuity and pointwise rectangle
convergence, including an empty family for a zero supplied functional. -/
theorem rectangularSectionIntegrand_regular (j k : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (t + (j + k + 1) + 1) F) V)
    (hπ : IsOfWhittakerType (t + (j + k + 1))
      (standardCharacter ψ (t + (j + k + 1))) π)
    (lambda : glFunctionals ψ (t + (j + k + 1)) π)
    (Wtest : (coefficientModel π lambda).toSubmodule)
    (ν : AdditiveHaarMeasure F)
    (weight : LeftUnipotentQuotient t F → ℂ) (hw : Continuous weight) :
    Continuous (fun z : BlockQuotient h F ×
        Matrix (Fin j) (Fin (t + 1)) F =>
      rectangularSectionIntegrand F ell f j k Wtest.val weight z.2 z.1) ∧
    (∀ z, Integrable (fun x =>
      rectangularSectionIntegrand F ell f j k Wtest.val weight x z)
      (rectangularMeasure ν j (t + 1))) ∧
    Continuous (rectangularSectionAverage F ell f j k Wtest.val ν weight) := by
  classical
  obtain ⟨d, φ, fs, he⟩ := exists_rectangularSectionExpansion F j k π hπ lambda Wtest
  let D (i : Fin d) := sectionIntegrand F ell f
    (diagonalWhittaker ψ (j + k + 1) (fs i).val) weight
  have hD (i : Fin d) : Continuous (D i) := by
    apply sectionIntegrand_continuous F ell f _ weight _ hw
    exact (glModelFunction_continuous ψ _ π hπ.1.1 lambda (fs i)).comp
      (firstQuotient_continuous_appendIdentity F t (j + k + 1))
  have hφ (i : Fin d) : Integrable (φ i) (rectangularMeasure ν j (t + 1)) :=
    Langlands.AllField.RankinSelberg.UnequalRankReduction.padic_rectangular_schwartz_integrable
      F (⟨⟩ : LocalFieldData F) j (t + 1) ν (φ i)
  have e (x : Matrix (Fin j) (Fin (t + 1)) F)
      (z : BlockQuotient h F) :
      rectangularSectionIntegrand F ell f j k Wtest.val weight x z =
        ∑ i, D i z * φ i x :=
    rectangularSectionIntegrand_expansion F ell f j k d Wtest.val weight
      (fun i => (φ i : _ → ℂ)) (fun i => (fs i).val) he x z
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [e]
    exact continuous_finsetSum _ fun i _ =>
      ((hD i).comp continuous_fst).mul ((φ i).continuous.comp continuous_snd)
  · intro z
    simp_rw [e]
    exact integrable_finsetSum _ fun i _ => (hφ i).const_mul (D i z)
  · have eavg : rectangularSectionAverage F ell f j k Wtest.val ν weight =
        fun z => ∑ i, D i z * ∫ x, φ i x ∂rectangularMeasure ν j (t + 1) := by
      funext z
      unfold rectangularSectionAverage
      simp_rw [e]
      rw [integral_finsetSum _ (fun i _ => (hφ i).const_mul (D i z))]
      simp_rw [integral_const_mul]
    rw [eavg]
    exact continuous_finsetSum _ fun i _ => (hD i).mul_const _

/-- Exact first-block quotient unfolding of the actual rectangle average, at
small slice `a` over the fixed mixed slice zero. -/
theorem rectangularSectionAverage_firstBlock_unfolding (j k : ℕ)
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
    let E := rectangularSectionAverage F ell f j k Wtest.val ν weight
    let B := Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.firstBlockAverage F h νA hInv a E
    let μM := νM.restrict (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.determinantSlice F h 0)
    Measurable B ∧ Integrable B μM ∧
      (∫ z, E z ∂νH.restrict (Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.determinantSlice F h a)) =
        ∫ q, B q ∂μM := by
  dsimp only
  let hInv := Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.normOneRightInvariant_of_isCompatible F (m 0)
    (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) νA hνA
  let κ := Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.fiberKernel F h νA hInv a
  have hκ := Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.fiberKernel_mk F h νA hInv a
  have hzero := (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.normalized_tower F h
    νA hInv hνA νM hνM νH hνH).2
  have hcomp := Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.fiberKernel_comp_zeroSlice_eq F h
    νA hInv hνA νM hνM νH hzero a
  have hEc := (rectangularSectionIntegrand_regular F ell f j k π hπ lambda Wtest ν
    weight hw).2.2
  have hEp := rectangularSectionIntegrand_integrable F ell f j k π hπ lambda Wtest
    weight hw μR hraw ν νN νH hνN hνH a
  have hEi := hEp.integral_prod_left
  have he := Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.firstBlockAverage_eq_integral_kernel F h νA
    hInv a κ hκ _ hEc.measurable
  have hBm : Measurable (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.firstBlockAverage F h νA hInv a
      (rectangularSectionAverage F ell f j k Wtest.val ν weight)) := by
    rw [he]
    exact (hEc.measurable.stronglyMeasurable.integral_kernel (κ := κ)).measurable
  have hBo := ((Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.analytic_of_comp_eq F h νA hInv a κ hκ
    _ _ hcomp).2 _ hEc.measurable).2 hEi
  exact ⟨hBm, hBo⟩

end Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
