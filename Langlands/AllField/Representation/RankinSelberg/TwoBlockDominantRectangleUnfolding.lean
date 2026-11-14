import Langlands.Representation.RankinSelberg.TwoBlockDominantRectangleUnfolding
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantSectionUnfolding
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantUpperSliceAnalysis
/-! # Product convergence for the actual rectangular section integrand -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg.TwoBlockDominantFirstBlock hiding UpperSliceConverges continuous_diagonalIntegrand continuous_upperAverage diagonalSupportGLTopological diagonalSupportT2 diagonalSupportTopology diagonalWhittaker_slice_hasCompactSupport exists_rectangularSectionExpansion exists_uniformOrdinaryJacquetRealization instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instIsNonarchimedeanLocalFieldCarrier instIsTopologicalGroupGeneralLinearCarrier instLocallyCompactSpaceGeneralLinearCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instSecondCountableTopologyCarrier instSecondCountableTopologyGeneralLinearCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instValuativeRelCarrier integrable_rectangularBorelMeasure rectangleUnfoldingCountable rectangleUnfoldingGLBorel rectangleUnfoldingGLCountable rectangleUnfoldingGLMeasurable rectangleUnfoldingGLTopology rectangleUnfoldingHBorel rectangleUnfoldingHMeasurable rectangleUnfoldingHQMeasurable rectangleUnfoldingLocalField rectangleUnfoldingMeasurable rectangleUnfoldingNBorel rectangleUnfoldingNCountable rectangleUnfoldingNMeasurable rectangleUnfoldingNQMeasurable rectangleUnfoldingT2 rectangleUnfoldingTopology rectangleUnfoldingValuation rectangularBorelMeasure rectangularSectionIntegrand rectangularSectionIntegrand_expansion rectangularSectionIntegrand_integrable rectangularSectionIntegrand_mk rectangularWhittaker rectangularWhittaker_apply sectionAverage_mk sectionAverages_continuous sectionIntegrand sectionIntegrand_continuous sectionIntegrand_fiberPoint sectionIntegrand_mk sectionIntegrand_slice_unfolding sectionNormAverage_mk sectionUnfoldingBorel sectionUnfoldingCountable sectionUnfoldingGLBorel sectionUnfoldingGLCountable sectionUnfoldingGLLocalCompact sectionUnfoldingGLMeasurable sectionUnfoldingGLTopology sectionUnfoldingHBorel sectionUnfoldingHMeasurable sectionUnfoldingHQBorel sectionUnfoldingHQMeasurable sectionUnfoldingLocalField sectionUnfoldingMeasurable sectionUnfoldingNBorel sectionUnfoldingNCountable sectionUnfoldingNMeasurable sectionUnfoldingNQBorel sectionUnfoldingNQMeasurable sectionUnfoldingT2 sectionUnfoldingTopology sectionUnfoldingValuation upperSliceConverges
open Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankLastRowReductionStatement EqualRankNormalizedCompactIntegrationStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockOrdinaryJacquetFunctionalStatement TwoBlockUnipotentQuotientIntegrationStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankLastRowReduction equalRankNormalizedCompactIntegration equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound finiteFunctionMellin finiteFunctionShellSeries hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductWhittakerType oneVariableMellin pairwise_disjoint_determinantSlice quotientIwasawaIntegration quotientRootIntegration rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight setIntegral_equalRankIntegrand_determinantSlice setIntegral_unequalRankAverage_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrableAt_unequalRankAverage_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val twoBlockOrdinaryJacquetFunctional twoBlockUnipotentQuotientIntegration unequalRankAnalytic unequalRankAverage unequalRankAverage_eq_mul_spectralPoint_zpow unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankIwasawaSupport unequalRankSliceCoefficient unequalRankSliceExpansion unequalRankSliceExpansion_of_converges unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unequalSliceMatrixMeasurable unequalSliceQuotientBorel unequalSliceQuotientMeasurable unequalSliceTopology whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
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

local instance rectangleUnfoldingT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance rectangleUnfoldingCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance rectangleUnfoldingGLTopology (a : ℕ) :
    IsTopologicalGroup (GeneralLinear a F) :=
  (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup a
local instance rectangleUnfoldingGLLocalCompact (a : ℕ) :
    LocallyCompactSpace (GeneralLinear a F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace a
local instance rectangleUnfoldingGLCountable (a : ℕ) :
    SecondCountableTopology (GeneralLinear a F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology a
local instance rectangleUnfoldingMeasurable : MeasurableSpace F := borel _
local instance rectangleUnfoldingBorel : BorelSpace F := ⟨rfl⟩
local instance rectangleUnfoldingGLMeasurable (a : ℕ) :
    MeasurableSpace (GeneralLinear a F) := borel _
local instance rectangleUnfoldingGLBorel (a : ℕ) :
    BorelSpace (GeneralLinear a F) := ⟨rfl⟩
local instance rectangleUnfoldingNMeasurable (a : ℕ) :
    MeasurableSpace (upperUnipotent a F) := borel _
local instance rectangleUnfoldingNBorel (a : ℕ) :
    BorelSpace (upperUnipotent a F) := ⟨rfl⟩
local instance rectangleUnfoldingNCountable (a : ℕ) :
    SecondCountableTopology (upperUnipotent a F) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance rectangleUnfoldingNQMeasurable (a : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient a F) := borel _
local instance rectangleUnfoldingNQBorel (a : ℕ) :
    BorelSpace (LeftUnipotentQuotient a F) := ⟨rfl⟩

variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}
  {ψ : UnitaryAdditiveCharacter F}

local instance rectangleUnfoldingHMeasurable :
    MeasurableSpace (blockUnipotent h F) := borel _
local instance rectangleUnfoldingHBorel :
    BorelSpace (blockUnipotent h F) := ⟨rfl⟩
local instance rectangleUnfoldingHQMeasurable :
    MeasurableSpace (BlockQuotient h F) := borel _
local instance rectangleUnfoldingHQBorel :
    BorelSpace (BlockQuotient h F) := ⟨rfl⟩

variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
  (f : Sections F h σ)

/-- At a fixed actual rectangle, the larger-rank test restricts to a Whittaker
function through the diagonal inclusion followed by that rectangle. -/
def rectangularWhittaker (j k : ℕ)
    (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))
    (x : Matrix (Fin j) (Fin (t + 1)) F) : WhittakerFunctions ψ t :=
  diagonalWhittaker ψ (j + k + 1)
    (translateWhittaker ψ (t + (j + k + 1)) Wtest (rectangularUnipotent j k x))

@[simp] theorem rectangularWhittaker_apply (j k : ℕ)
    (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))
    (x : Matrix (Fin j) (Fin (t + 1)) F)
    (g : GeneralLinear (t + 1) F) :
    (rectangularWhittaker F j k Wtest x).val g =
      Wtest.val (unequalRankMatrix j k g x) := rfl

/-- The actual scalar section times the actual unequal-rank test matrix,
descended in its group argument before any rectangular integration. -/
def rectangularSectionIntegrand (j k : ℕ)
    (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))
    (weight : LeftUnipotentQuotient t F → ℂ)
    (x : Matrix (Fin j) (Fin (t + 1)) F)
    (z : BlockQuotient h F) : ℂ :=
  sectionIntegrand F ell f (rectangularWhittaker F j k Wtest x) weight z

@[simp] theorem rectangularSectionIntegrand_mk (j k : ℕ)
    (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))
    (weight : LeftUnipotentQuotient t F → ℂ)
    (x : Matrix (Fin j) (Fin (t + 1)) F)
    (g : GeneralLinear (t + 1) F) :
    rectangularSectionIntegrand F ell f j k Wtest weight x (Quotient.mk _ g) =
      Wtest.val (unequalRankMatrix j k g x) *
        scalarSection (fun i => (ell i).val) f g 1 * weight (Quotient.mk _ g) := rfl

private theorem rectangle_continuous_appendIdentity (n d : ℕ) :
    Continuous (appendIdentity (F := F) n d) := by
  induction d with
  | zero => exact continuous_id
  | succ d ih => exact (GeneralLinear.rankInclusionContinuous 1).continuous.comp ih

private theorem rectangle_coefficient_continuous {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hπ : IsSmooth π) (lambda : glFunctionals ψ r π)
    (Wtest : (coefficientModel π lambda).toSubmodule) : Continuous Wtest.val.val := by
  obtain ⟨v, rfl⟩ := modelMap_surjective π lambda Wtest
  exact (matrixCoefficient_isLocallyConstant π lambda.val v (hπ v)).continuous

/-- The finite expansion is available also when the supplied functional is zero;
in that case the family is empty. -/
theorem exists_rectangularSectionExpansion (j k : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (t + (j + k + 1) + 1) F) V)
    (hπ : IsOfWhittakerType (t + (j + k + 1))
      (standardCharacter ψ (t + (j + k + 1))) π)
    (lambda : glFunctionals ψ (t + (j + k + 1)) π)
    (Wtest : (coefficientModel π lambda).toSubmodule) :
    ∃ (d : ℕ)
      (φ : Fin d → SchwartzBruhat (Matrix (Fin j) (Fin (t + 1)) F))
      (fs : Fin d → (coefficientModel π lambda).toSubmodule),
      ∀ (g : GeneralLinear (t + 1) F) x,
        Wtest.val.val (unequalRankMatrix j k g x) =
          ∑ i, φ i x * (fs i).val.val (appendIdentity t (j + k + 1) g) := by
  classical
  by_cases hlambda : lambda.val = 0
  · refine ⟨0, Fin.elim0, Fin.elim0, ?_⟩
    intro g x
    obtain ⟨v, rfl⟩ := modelMap_surjective π lambda Wtest
    change lambda.val (π (unequalRankMatrix j k g x) v) = _
    simp [hlambda]
  · exact unequalRankFiniteExpansion F (⟨⟩ : LocalFieldData F) t j k ψ V π hπ
      lambda hlambda Wtest (unequalRankCompactSupport F (⟨⟩ : LocalFieldData F)
        t j k ψ V π hπ lambda hlambda Wtest)

/-- The finite coefficient expansion gives a literal separated expansion on the
block quotient, retaining the scalar section and quotient weight. -/
theorem rectangularSectionIntegrand_expansion (j k d : ℕ)
    (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))
    (weight : LeftUnipotentQuotient t F → ℂ)
    (φ : Fin d → Matrix (Fin j) (Fin (t + 1)) F → ℂ)
    (fs : Fin d → WhittakerFunctions ψ (t + (j + k + 1)))
    (he : ∀ (g : GeneralLinear (t + 1) F) x,
      Wtest.val (unequalRankMatrix j k g x) =
        ∑ i, φ i x * (fs i).val (appendIdentity t (j + k + 1) g))
    (x : Matrix (Fin j) (Fin (t + 1)) F) (z : BlockQuotient h F) :
    rectangularSectionIntegrand F ell f j k Wtest weight x z =
      ∑ i, sectionIntegrand F ell f (diagonalWhittaker ψ (j + k + 1) (fs i)) weight z *
        φ i x := by
  induction z using Quotient.inductionOn with
  | h g =>
    simp only [rectangularSectionIntegrand_mk, sectionIntegrand_mk, he,
      diagonalWhittaker, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Genuine product-space convergence of the actual rectangular section
integrand. The finite expansion, raw Jacquet convergence and fixed-slice compact
norm support supply this independently of every small-block epsilon equation. -/
theorem rectangularSectionIntegrand_integrable (j k : ℕ)
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
    (νH : Measure (BlockQuotient h F))
    (hνN : IsCompatible (upperUnipotent (t + 1) F)
      (generalLinearHaar F t) (unipotentHaar F t) νN)
    (hνH : IsCompatible (blockUnipotent h F)
      (generalLinearHaar F t) (blockHaar F h) νH) (a : ℤ) :
    Integrable (fun z : BlockQuotient h F ×
        Matrix (Fin j) (Fin (t + 1)) F =>
      rectangularSectionIntegrand F ell f j k Wtest.val weight z.2 z.1)
      ((νH.restrict (projection h F ⁻¹'
        Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) t a)).prod
          (rectangularMeasure ν j (t + 1))) := by
  classical
  obtain ⟨d, φ, fs, he⟩ := exists_rectangularSectionExpansion F j k π hπ lambda Wtest
  have hdiag (i : Fin d) : Integrable
      (sectionIntegrand F ell f (diagonalWhittaker ψ (j + k + 1) (fs i).val) weight)
      (νH.restrict (projection h F ⁻¹'
        Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) t a)) := by
    have hc : Continuous (diagonalWhittaker ψ (j + k + 1) (fs i).val).val :=
      (rectangle_coefficient_continuous F π hπ.1.1 lambda (fs i)).comp
        (rectangle_continuous_appendIdentity F t (j + k + 1))
    exact (sectionIntegrand_slice_unfolding F ell f _ weight μR hc hw hraw νN νH
      hνN hνH a (diagonalWhittaker_slice_hasCompactSupport F t (j + k) ψ
        π hπ.1.1 lambda (fs i) a)).1
  have hφ (i : Fin d) : Integrable (φ i) (rectangularMeasure ν j (t + 1)) :=
    Langlands.AllField.RankinSelberg.UnequalRankReduction.padic_rectangular_schwartz_integrable
      F (⟨⟩ : LocalFieldData F) j (t + 1) ν (φ i)
  simp_rw [rectangularSectionIntegrand_expansion F ell f j k d Wtest.val weight
    (fun i => (φ i : _ → ℂ)) (fun i => (fs i).val) he]
  exact UnequalRankReduction.integrable_separated_sum Finset.univ _ _
    (fun i _ => hdiag i) (fun i _ => hφ i)

end Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
