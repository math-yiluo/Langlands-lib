import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualDuality
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantDualKernel
import Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergenceStatement
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFourierAnalytic
/-! # Actual duality at the equal-rank boundary -/

noncomputable section

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement TwoBlockRowFourierCompanionStatement padicMatrixFourierSlice padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling twoBlockRowFourierCompanion
open Langlands.AllField.HarmonicAnalysis

open _root_.MeasureTheory

section InverseCharacter


end InverseCharacter

end Langlands.AllField.HarmonicAnalysis

namespace Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg.DominantRankTransport hiding EqualLowerFourierCoefficientLaw determinantComplexPower_inverseTranspose equalDualityBorel equalDualityGLBorel equalDualityGLMeasurable equalDualityLocalField equalDualityLowerBorel equalDualityLowerMeasurable equalDualityMeasurable equalDualityQuotientMeasurable equalDualityTopology equalDualityUnipotentBorel equalDualityUnipotentMeasurable equalDualityValuation equalLowerFourierCoefficientLaw equalLowerGroupIntegrand_reversedDual equalLowerIntegrand_reversedDual negatedSelfDualHaar negatedSelfDualHaar_val reversedDual_oppositeTwistBlocks
open Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt TwoBlockDualSectionJacquetStatement TwoBlockJacquetConvergenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankContinuedForms equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockDualSectionJacquet twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement TwoBlockRowFourierCompanionStatement padicMatrixFourierSlice padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling twoBlockRowFourierCompanion
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockDominantRectangular hiding AbsoluteInput FiberIntegrable KernelAbsoluteIntegrable KernelNormProfileIntegrable KernelOuterIntegrable NormProfileIntegrable OuterIntegrable absoluteInput_standard_iff ae_lowerQuotientMeasure_iff determinantWeight_lowerBlockUnipotent_mul dualKernelLocalField dualKernelMeasurable dualKernelTopology dualKernelValuation dualRectangleBorel dualRectangleLocalField dualRectangleMatrixBorel dualRectangleMatrixSecondCountable dualRectangleMeasurable dualRectangleProductBorel dualRectangleSecondCountable dualRectangleTopology dualRectangleValuation fiberIntegrable_lowerBlockUnipotent_mul_iff integrable_lowerQuotientMeasure_iff integrable_rectangleChange_iff integral_dualRectangleEquiv integral_rectangleChange kernel kernelAbsoluteIntegrable_iff kernelAbsoluteIntegrable_standard_iff kernel_covariance kernel_eq kernel_reversedDual measurePreserving_dualRectangleEquiv measurePreserving_rectangleChange outerFieldT2 outerFieldTopology outerFieldValuation outerGeneralLinearGroup outerGeneralLinearLocallyCompact outerGeneralLinearSecondCountable outerLocalField quotientFiberIntegrable quotientKernel quotientKernelMeasurable quotientKernelTopology quotientKernel_mk quotientKernel_reversedDual quotientNormProfile quotientNormProfile_mk rawKernel rawKernel_covariance rawKernel_reversedDual rawScalarValue rectangleChangeHomeomorph rectangleHaarBorel rectangleHaarLocalField rectangleHaarMeasurable rectangleHaarSecondCountable rectangleHaarTopology rectangleHaarValuation rectangleMatrixBorel rectangleMatrixSecondCountable rectangleMeasure rectangleMeasure_sigmaFinite rectanglesBorel representativeKernel representativeKernel_lowerBlockUnipotent_mul representativeKernel_reversedDual representativeNormProfile representativeNormProfile_lowerBlockUnipotent_mul reversedDualSectionEquiv reversedDualSectionEquiv_scalar standardCompatible standardCompatible_sigmaFinite
open Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance equalDualityT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance equalDualitySecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance equalDualityMeasurable : MeasurableSpace F := borel _
local instance equalDualityBorel : BorelSpace F := ⟨rfl⟩
local instance equalDualityDisconnected : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

/-- The supplied self-dual measure, with its inverse-character certificate. -/
def negatedSelfDualHaar (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ) :
    Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) (ψ.scale (-1)) :=
  ⟨ν.val, ν.property.scale_neg_one ψ ν.val⟩

@[simp] theorem negatedSelfDualHaar_val (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ) :
    (negatedSelfDualHaar F ψ ν).val = ν.val := rfl

/-- Inverse transpose negates every complex determinant-power exponent. -/
theorem determinantComplexPower_inverseTranspose (n : ℕ) (s : ℂ) :
    ((⟨⟩ : LocalFieldData F).determinantComplexPower n s).comp
        (inverseTranspose n F).toMonoidHom =
      (⟨⟩ : LocalFieldData F).determinantComplexPower n (-s) := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  simp only [MonoidHom.comp_apply,
    Langlands.LocalFieldData.determinantComplexPower_apply]
  change (((⟨⟩ : LocalFieldData F).determinantNorm n
      (inverseTranspose n F g) : NNReal) : ℂ) ^ s =
    (((⟨⟩ : LocalFieldData F).determinantNorm n g : NNReal) : ℂ) ^ (-s)
  simp only [
    Langlands.LocalFieldData.determinantNorm_inverseTranspose,
    Units.val_inv_eq_inv_val, NNReal.coe_inv, Complex.ofReal_inv]
  rw [Complex.inv_cpow_ofReal_nonneg (NNReal.coe_nonneg _) s, Complex.cpow_neg]

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]

local instance equalDualityGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance equalDualityGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance equalDualityUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance equalDualityUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
local instance equalDualityQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F) := borel _
local instance equalDualityQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
local instance equalDualityLowerMeasurable :
    MeasurableSpace (TwoBlockLowerUnipotentQuotient.LowerQuotient h F) := borel _
local instance equalDualityLowerBorel :
    BorelSpace (TwoBlockLowerUnipotentQuotient.LowerQuotient h F) := ⟨rfl⟩
local instance equalDualityReverseLowerMeasurable :
    MeasurableSpace (TwoBlockLowerUnipotentQuotient.LowerQuotient (reverse_sum h) F) :=
  borel _
local instance equalDualityReverseLowerBorel :
    BorelSpace (TwoBlockLowerUnipotentQuotient.LowerQuotient (reverse_sum h) F) := ⟨rfl⟩

/-- Complete reversal and inverse transpose preserve the opposite-twist parameter. -/
theorem reversedDual_oppositeTwistBlocks
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (u : ℝ) :
    (fun i : Fin 2 => inverseTransposePullback (twoBlockOppositeTwistBlocks F m τ u i.rev)) =
      twoBlockOppositeTwistBlocks F (fun i => m i.rev)
        (fun i => inverseTransposePullback (τ i.rev)) u := by
  funext i
  unfold inverseTransposePullback twoBlockOppositeTwistBlocks
  rw [twist_comp, determinantComplexPower_inverseTranspose]
  have he : -(if i.rev = 0 then -(u : ℂ) else (u : ℂ)) =
      (if i = 0 then -(u : ℂ) else (u : ℂ)) := by
    fin_cases i <;> simp
  rw [he]

open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockLowerUnfolding hiding groupIntegrand groupIntegrand_def groupIntegrand_lowerBlockUnipotent_mul integrand integrand_mk integrand_mk_eq_groupIntegrand isTopologicalRing_carrier partialSection partialSection_apply partialSection_lowerBlockUnipotent_mul rowMeasure_map_vecMul_upperUnipotent scalarSection_lowerBlockUnipotent_mul sigmaFinite_additiveHaarMeasure whittaker_blockRotation_lowerBlockUnipotent_mul
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding
open Langlands.RankinSelberg.TwoBlockLowerFourier hiding lowerDuality_measure_transport lowerDuality_order lowerDuality_slices lowerDuality_symm_order ord_determinant_dual ord_determinant_weylLong partialSection_fourier rowCompanion_contiguous
open Langlands.AllField.RankinSelberg.TwoBlockLowerFourier

variable (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
  (hσ : ∀ i, IsSmooth (σ i))
  (ψ : UnitaryAdditiveCharacter F)
  (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
  (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)

/-- The fixed section equivalence discharges the scalar-section premise in
the published Fourier comparison. -/
theorem equalLowerGroupIntegrand_reversedDual
    (f : Sections F h σ) (Wtest : WhittakerFunctions ψ t)
    (Φ Φhat : SchwartzBruhat (Fin (t + 1) → F))
    (hpair : IsRowFourierPair ψ ν.val Φ Φhat)
    (g : GeneralLinear (t + 1) F) :
    groupIntegrand (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
        (reversedDualSectionEquiv F h σ hσ f) (firstDualFunction ψ t Wtest)
        Φhat ν.val (weylLong (t + 1) F * inverseTranspose (t + 1) F g) =
      ((⟨⟩ : LocalFieldData F).normalizedAbs (determinant g : F) : ℂ) *
        groupIntegrand ell f Wtest Φ ν.val g := by
  rw [groupIntegrand_def, groupIntegrand_def,
    lowerDualTest_rotation h ψ Wtest,
    reversedDualSectionEquiv_scalar F h σ hσ ψ ell]
  have hinv := weylInverseTranspose_involutive (t + 1) F g
  simp only [weylInverseTranspose_apply] at hinv
  rw [hinv, partialSection_fourier F h ψ ν.val ν.property Φ Φhat hpair]
  ring

/-- The pointwise comparison descends along the actual lower duality. -/
theorem equalLowerIntegrand_reversedDual
    (f : Sections F h σ) (Wtest : WhittakerFunctions ψ t)
    (Φ Φhat : SchwartzBruhat (Fin (t + 1) → F))
    (hpair : IsRowFourierPair ψ ν.val Φ Φhat)
    (z : LowerQuotient h F) :
    integrand (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
        (reversedDualSectionEquiv F h σ hσ f) (firstDualFunction ψ t Wtest)
        Φhat ν.val (lowerDuality F h z) =
      ((((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
        (-Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantOrder F h z) : ℝ) : ℂ) *
        integrand ell f Wtest Φ ν.val z := by
  induction z using Quotient.inductionOn with
  | h g =>
    rw [lowerDuality_mk, integrand_mk_eq_groupIntegrand,
      integrand_mk_eq_groupIntegrand,
      equalLowerGroupIntegrand_reversedDual F h σ hσ ψ ell ν f Wtest Φ Φhat hpair g,
      Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantOrder_mk,
      (⟨⟩ : LocalFieldData F).normalizedAbs_of_ne_zero (determinant g).ne_zero]

/-- The actual equal-rank lower coefficient law, including integrability and
the raw-norm integral, for the supplied standard quotient measure. -/
def EqualLowerFourierCoefficientLaw
    (μN : Measure (LeftUnipotentQuotient t F)) : Prop :=
  ∀ (f : Sections F h σ) (Wtest : WhittakerFunctions ψ t)
    (Φ Φhat : SchwartzBruhat (Fin (t + 1) → F)),
    IsRowFourierPair ψ ν.val Φ Φhat → ∀ k : ℤ,
      let E := integrand ell f Wtest Φ ν.val
      let ED := integrand (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
        (reversedDualSectionEquiv F h σ hσ f) (firstDualFunction ψ t Wtest) Φhat ν.val
      let μL := lowerQuotientMeasure F h μN
      let μD := lowerQuotientMeasure F (reverse_sum h) μN
      (Integrable ED
          (μD.restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-k))) ↔
        Integrable E
          (μL.restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k))) ∧
      (∫ z, ED z
          ∂μD.restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-k))) =
        ((⟨⟩ : LocalFieldData F).residueCardinality : ℂ) ^ (-k) *
          (∫ z, E z
            ∂μL.restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k)) ∧
      (∫ z, ‖ED z‖
          ∂μD.restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-k))) =
        ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^ (-k) *
          (∫ z, ‖E z‖
            ∂μL.restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k))

/-- The actual section equivalence and published supplied-measure transport
prove the coefficient law, with no scalar-section comparison premise. -/
theorem equalLowerFourierCoefficientLaw
    [hN : Measure.IsMulRightInvariant (unipotentHaar F t)]
    (μN : Measure (LeftUnipotentQuotient t F))
    (hμN : IsCompatible (upperUnipotent (t + 1) F)
      (generalLinearHaar F t) (unipotentHaar F t) μN) :
    EqualLowerFourierCoefficientLaw F h σ hσ ψ ell ν μN := by
  intro f Wtest Φ Φhat hpair k
  dsimp only
  let E := integrand ell f Wtest Φ ν.val
  let ED := integrand (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
    (reversedDualSectionEquiv F h σ hσ f) (firstDualFunction ψ t Wtest) Φhat ν.val
  let μL := lowerQuotientMeasure F h μN
  let μD := lowerQuotientMeasure F (reverse_sum h) μN
  have hm := lowerDuality_measure_transport F h hN μN hμN
  have hDslice : MeasurePreserving (lowerDuality F h)
      (μL.restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k))
      (μD.restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-k))) :=
    ⟨(lowerDuality F h).continuous.measurable, (hm.2.2 k).1⟩
  have hE : ∀ᵐ z ∂μL.restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k),
      ED (lowerDuality F h z) =
        ((((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^ (-k) : ℝ) : ℂ) * E z := by
    filter_upwards [ae_restrict_mem
      (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.isClopen_determinantSlice F h k).1.measurableSet] with z hz
    have hk := (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.mem_determinantSlice_iff_determinantOrder F h).mp hz
    simpa only [hk] using
      equalLowerIntegrand_reversedDual F h σ hσ ψ ell ν f Wtest Φ Φhat hpair z
  have hq : 0 < ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) := by
    exact_mod_cast Nat.zero_lt_one.trans (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
  have hs := scalar_transport (lowerDuality F h).toMeasurableEquiv
    hDslice E ED (((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^ (-k))
    (zpow_pos hq _) hE
  simpa only [Complex.ofReal_zpow, Complex.ofReal_natCast] using hs

end Langlands.AllField.RankinSelberg.DominantRankTransport
