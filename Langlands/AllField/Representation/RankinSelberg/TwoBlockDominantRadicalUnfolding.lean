import Langlands.Representation.RankinSelberg.TwoBlockDominantRadicalUnfolding
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantRectangleUnfolding
/-! # Integrated radical unfolding of the actual unequal-rank section -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg.TwoBlockDominantFirstBlock hiding UpperSliceConverges continuous_diagonalIntegrand continuous_upperAverage diagonalSupportGLTopological diagonalSupportT2 diagonalSupportTopology diagonalWhittaker_slice_hasCompactSupport exists_rectangularSectionExpansion exists_uniformOrdinaryJacquetRealization instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instIsNonarchimedeanLocalFieldCarrier instIsTopologicalGroupGeneralLinearCarrier instLocallyCompactSpaceGeneralLinearCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instSecondCountableTopologyCarrier instSecondCountableTopologyGeneralLinearCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instValuativeRelCarrier integrable_rectangularBorelMeasure quotientDeterminantWeight quotientDeterminantWeight_continuous quotientDeterminantWeight_mk radicalUnfoldingBorel radicalUnfoldingCountable radicalUnfoldingGLBorel radicalUnfoldingGLCountable radicalUnfoldingGLMeasurable radicalUnfoldingGLTopology radicalUnfoldingHBorel radicalUnfoldingHMeasurable radicalUnfoldingHQMeasurable radicalUnfoldingLocalField radicalUnfoldingMeasurable radicalUnfoldingNBorel radicalUnfoldingNCountable radicalUnfoldingNMeasurable radicalUnfoldingNQMeasurable radicalUnfoldingT2 radicalUnfoldingTopology radicalUnfoldingValuation rectangleUnfoldingCountable rectangleUnfoldingGLBorel rectangleUnfoldingGLCountable rectangleUnfoldingGLMeasurable rectangleUnfoldingGLTopology rectangleUnfoldingHBorel rectangleUnfoldingHMeasurable rectangleUnfoldingHQMeasurable rectangleUnfoldingLocalField rectangleUnfoldingMeasurable rectangleUnfoldingNBorel rectangleUnfoldingNCountable rectangleUnfoldingNMeasurable rectangleUnfoldingNQMeasurable rectangleUnfoldingT2 rectangleUnfoldingTopology rectangleUnfoldingValuation rectangularBorelMeasure rectangularSectionIntegrand rectangularSectionIntegrand_expansion rectangularSectionIntegrand_integrable rectangularSectionIntegrand_mk rectangularSection_slice_unfolding rectangularWhittaker rectangularWhittaker_apply sectionAverage_mk sectionAverages_continuous sectionIntegrand sectionIntegrand_continuous sectionIntegrand_fiberPoint sectionIntegrand_mk sectionIntegrand_slice_unfolding sectionNormAverage_mk sectionUnfoldingBorel sectionUnfoldingCountable sectionUnfoldingGLBorel sectionUnfoldingGLCountable sectionUnfoldingGLLocalCompact sectionUnfoldingGLMeasurable sectionUnfoldingGLTopology sectionUnfoldingHBorel sectionUnfoldingHMeasurable sectionUnfoldingHQBorel sectionUnfoldingHQMeasurable sectionUnfoldingLocalField sectionUnfoldingMeasurable sectionUnfoldingNBorel sectionUnfoldingNCountable sectionUnfoldingNMeasurable sectionUnfoldingNQBorel sectionUnfoldingNQMeasurable sectionUnfoldingT2 sectionUnfoldingTopology sectionUnfoldingValuation upperSliceConverges
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

local instance radicalUnfoldingT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance radicalUnfoldingCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance radicalUnfoldingGLTopology (a : ℕ) :
    IsTopologicalGroup (GeneralLinear a F) :=
  (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup a
local instance radicalUnfoldingGLLocalCompact (a : ℕ) :
    LocallyCompactSpace (GeneralLinear a F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace a
local instance radicalUnfoldingGLCountable (a : ℕ) :
    SecondCountableTopology (GeneralLinear a F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology a
local instance radicalUnfoldingMeasurable : MeasurableSpace F := borel _
local instance radicalUnfoldingBorel : BorelSpace F := ⟨rfl⟩
local instance radicalUnfoldingGLMeasurable (a : ℕ) :
    MeasurableSpace (GeneralLinear a F) := borel _
local instance radicalUnfoldingGLBorel (a : ℕ) :
    BorelSpace (GeneralLinear a F) := ⟨rfl⟩
local instance radicalUnfoldingNMeasurable (a : ℕ) :
    MeasurableSpace (upperUnipotent a F) := borel _
local instance radicalUnfoldingNBorel (a : ℕ) :
    BorelSpace (upperUnipotent a F) := ⟨rfl⟩
local instance radicalUnfoldingNCountable (a : ℕ) :
    SecondCountableTopology (upperUnipotent a F) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance radicalUnfoldingNQMeasurable (a : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient a F) := borel _
local instance radicalUnfoldingNQBorel (a : ℕ) :
    BorelSpace (LeftUnipotentQuotient a F) := ⟨rfl⟩

variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}
  {ψ : UnitaryAdditiveCharacter F}

local instance radicalUnfoldingHMeasurable :
    MeasurableSpace (blockUnipotent h F) := borel _
local instance radicalUnfoldingHBorel :
    BorelSpace (blockUnipotent h F) := ⟨rfl⟩
local instance radicalUnfoldingHQMeasurable :
    MeasurableSpace (BlockQuotient h F) := borel _
local instance radicalUnfoldingHQBorel :
    BorelSpace (BlockQuotient h F) := ⟨rfl⟩

/-- The actual determinant weight on the standard unipotent quotient. -/
def quotientDeterminantWeight (n : ℕ) (s : ℂ)
    (q : LeftUnipotentQuotient n F) : ℂ :=
  (quotientDeterminantAbs (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) n q : ℂ) ^ s

@[simp] theorem quotientDeterminantWeight_mk (n : ℕ) (s : ℂ)
    (g : GeneralLinear (n + 1) F) :
    quotientDeterminantWeight F n s (Quotient.mk _ g) =
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g s := rfl

theorem quotientDeterminantWeight_continuous (n : ℕ) (s : ℂ) :
    Continuous (quotientDeterminantWeight F n s) := by
  apply (leftQuotient_isOpenQuotientMap
    (upperUnipotent (n + 1) F)).isQuotientMap.continuous_iff.mpr
  have hdet : Continuous (fun g : GeneralLinear (n + 1) F =>
      normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) (Matrix.det g.val)) :=
    (NNReal.continuous_coe.comp (⟨⟩ : LocalFieldData F).continuous_normalizedAbsHom).comp
      Units.continuous_val.matrix_det
  exact (Complex.continuous_ofReal.comp hdet).cpow continuous_const
    (fun g => Complex.ofReal_mem_slitPlane.mpr
      ((normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)).pos g.det_ne_zero))

variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
  (f : Sections F h σ)
  (μR : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
  [μR.IsAddHaarMeasure]
  (Wjac : InverseWhittakerFunctions ψ t)
  (hjac : ∀ g : GeneralLinear (t + 1) F,
    Wjac.val g = jacquetFunction ψ (fun i => (ell i).val) μR f g)

private theorem radical_continuous_appendIdentity (n d : ℕ) :
    Continuous (appendIdentity (F := F) n d) := by
  induction d with
  | zero => exact continuous_id
  | succ d ih => exact (GeneralLinear.rankInclusionContinuous 1).continuous.comp ih

private theorem radical_coefficient_continuous {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hπ : IsSmooth π) (lambda : glFunctionals ψ r π)
    (Wtest : (coefficientModel π lambda).toSubmodule) : Continuous Wtest.val.val := by
  obtain ⟨v, rfl⟩ := modelMap_surjective π lambda Wtest
  exact (matrixCoefficient_isLocallyConstant π lambda.val v (hπ v)).continuous

include hjac in
/-- Raw Jacquet convergence gives genuine product convergence on both sides
and the normalized unfolding after integrating the actual external rectangle. -/
theorem rectangularSection_slice_unfolding (j k : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (t + (j + k + 1) + 1) F) V)
    (hπ : IsOfWhittakerType (t + (j + k + 1))
      (standardCharacter ψ (t + (j + k + 1))) π)
    (lambda : glFunctionals ψ (t + (j + k + 1)) π)
    (Wtest : (coefficientModel π lambda).toSubmodule)
    (hraw : IsAbsIntegrable ψ (fun i => (ell i).val) μR f)
    (ν : AdditiveHaarMeasure F)
    (νN : Measure (LeftUnipotentQuotient t F)) [SigmaFinite νN]
    (νH : Measure (BlockQuotient h F)) [SigmaFinite νH]
    (hνN : IsCompatible (upperUnipotent (t + 1) F)
      (generalLinearHaar F t) (unipotentHaar F t) νN)
    (hνH : IsCompatible (blockUnipotent h F)
      (generalLinearHaar F t) (blockHaar F h) νH) (a : ℤ) (s : ℂ) :
    let weight := quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2)
    let slice := Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) t a
    let E := rectangularSectionIntegrand F ell f j k Wtest.val weight
    let c := μR {x | ∀ i j, x i j ∈ (ValuativeRel.valuation F).integer}
    Integrable (fun z : LeftUnipotentQuotient t F ×
        Matrix (Fin j) (Fin (t + 1)) F =>
      unequalRankIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        j k Wtest.val Wjac s z.2 z.1)
      ((νN.restrict slice).prod (rectangularMeasure ν j (t + 1))) ∧
    Integrable (fun z : BlockQuotient h F ×
        Matrix (Fin j) (Fin (t + 1)) F => E z.2 z.1)
      ((νH.restrict (projection h F ⁻¹' slice)).prod
        (rectangularMeasure ν j (t + 1))) ∧
    (∫ q, ∫ x, unequalRankIntegrand ψ
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) j k Wtest.val Wjac s x q
        ∂rectangularMeasure ν j (t + 1) ∂νN.restrict slice) =
      c.toReal • (∫ z, ∫ x, E x z ∂rectangularMeasure ν j (t + 1)
        ∂νH.restrict (projection h F ⁻¹' slice)) := by
  classical
  dsimp only
  let weight := quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2)
  let slice := Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) t a
  let c := μR {x | ∀ i j, x i j ∈ (ValuativeRel.valuation F).integer}
  have hw : Continuous weight := quotientDeterminantWeight_continuous F t _
  let : SigmaFinite ν.measure := inferInstance
  obtain ⟨d, φ, fs, he⟩ := exists_rectangularSectionExpansion F j k π hπ lambda Wtest
  let DH (i : Fin d) := sectionIntegrand F ell f
    (diagonalWhittaker ψ (j + k + 1) (fs i).val) weight
  let DN (i : Fin d) := unequalRankIntegrand ψ
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) j k (fs i).val Wjac s 0
  have havg (i : Fin d) : radicalAverage F h μR (DH i) = DN i := by
    funext q
    induction q using Quotient.inductionOn with
    | h g =>
      simp only [DH, DN, sectionAverage_mk, unequalRankIntegrand_mk,
        UnequalRankReduction.unequalRankMatrix_at_zero, weight, quotientDeterminantWeight_mk]
      rw [hjac]
      rfl
  have hdiag (i : Fin d) : Integrable (DH i)
      (νH.restrict (projection h F ⁻¹' slice)) ∧
      Integrable (DN i) (νN.restrict slice) ∧
      (∫ q, DN i q ∂νN.restrict slice) =
        c.toReal • (∫ z, DH i z ∂νH.restrict (projection h F ⁻¹' slice)) := by
    have hc : Continuous (diagonalWhittaker ψ (j + k + 1) (fs i).val).val :=
      (radical_coefficient_continuous F π hπ.1.1 lambda (fs i)).comp
        (radical_continuous_appendIdentity F t (j + k + 1))
    obtain ⟨hH, _, hN, hEq⟩ := sectionIntegrand_slice_unfolding F ell f _ weight μR
      hc hw hraw νN νH hνN hνH a
      (diagonalWhittaker_slice_hasCompactSupport F t (j + k) ψ π hπ.1.1 lambda (fs i) a)
    rw [havg] at hN hEq
    exact ⟨hH, hN, hEq⟩
  have hφ (i : Fin d) : Integrable (φ i) (rectangularMeasure ν j (t + 1)) :=
    Langlands.AllField.RankinSelberg.UnequalRankReduction.padic_rectangular_schwartz_integrable
      F (⟨⟩ : LocalFieldData F) j (t + 1) ν (φ i)
  have eN (x : Matrix (Fin j) (Fin (t + 1)) F)
      (q : LeftUnipotentQuotient t F) :
      unequalRankIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        j k Wtest.val Wjac s x q = ∑ i, DN i q * φ i x :=
    UnequalRankReduction.integrand_of_finite_expansion ψ
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) j k d Wtest.val Wjac
      (fun i => (φ i : _ → ℂ)) (fun i => (fs i).val) he s x q
  have eH (x : Matrix (Fin j) (Fin (t + 1)) F)
      (z : BlockQuotient h F) :
      rectangularSectionIntegrand F ell f j k Wtest.val weight x z =
        ∑ i, DH i z * φ i x :=
    rectangularSectionIntegrand_expansion F ell f j k d Wtest.val weight
      (fun i => (φ i : _ → ℂ)) (fun i => (fs i).val) he x z
  have hNp : Integrable (fun z : LeftUnipotentQuotient t F ×
      Matrix (Fin j) (Fin (t + 1)) F =>
      unequalRankIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        j k Wtest.val Wjac s z.2 z.1)
      ((νN.restrict slice).prod (rectangularMeasure ν j (t + 1))) := by
    simp_rw [eN]
    exact UnequalRankReduction.integrable_separated_sum Finset.univ _ _
      (fun i _ => (hdiag i).2.1) (fun i _ => hφ i)
  have hHp := rectangularSectionIntegrand_integrable F ell f j k π hπ lambda Wtest
    weight hw μR hraw ν νN νH hνN hνH a
  refine ⟨hNp, hHp, ?_⟩
  calc
    _ = ∫ x, ∫ q, unequalRankIntegrand ψ
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) j k Wtest.val Wjac s x q
          ∂νN.restrict slice ∂rectangularMeasure ν j (t + 1) :=
      integral_integral_swap hNp
    _ = ∫ x, c.toReal • (∫ z,
        rectangularSectionIntegrand F ell f j k Wtest.val weight x z
          ∂νH.restrict (projection h F ⁻¹' slice))
            ∂rectangularMeasure ν j (t + 1) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp_rw [eN, eH]
        rw [integral_finsetSum _ (fun i _ => ((hdiag i).2.1).mul_const (φ i x)),
          integral_finsetSum _ (fun i _ => ((hdiag i).1).mul_const (φ i x))]
        simp_rw [integral_mul_const, (hdiag _).2.2]
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact smul_mul_assoc c.toReal _ (φ i x)
    _ = c.toReal • (∫ x, ∫ z,
        rectangularSectionIntegrand F ell f j k Wtest.val weight x z
          ∂νH.restrict (projection h F ⁻¹' slice)
            ∂rectangularMeasure ν j (t + 1)) := integral_smul _ _
    _ = _ := congrArg (fun v : ℂ => c.toReal • v) (integral_integral_swap hHp.swap)

end Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
