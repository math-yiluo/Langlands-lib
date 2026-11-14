import Langlands.Representation.RankinSelberg.TwoBlockDominantStrictFirstBlock
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantEqualSecondBlock
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantFirstBlockLaurentIdentityStatement
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantStrictNumerators
noncomputable section

namespace Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg.DominantRankTransport hiding EqualFirstBlockCoefficientLaw EqualLowerFourierCoefficientLaw EqualTwoSidedFirstBlockLaws StrictFirstBlockCoefficientLaw StrictFirstBlockFactorCertificate coe_strictResidueCardinalityUnit determinantComplexPower_inverseTranspose determinantComplexPower_weylLong dualJacquetLocalField dualJacquetTopology dualJacquetValuation equalDualityBorel equalDualityGLBorel equalDualityGLMeasurable equalDualityLocalField equalDualityLowerBorel equalDualityLowerMeasurable equalDualityMeasurable equalDualityQuotientMeasurable equalDualityTopology equalDualityUnipotentBorel equalDualityUnipotentMeasurable equalDualityValuation equalFirstBlockBorel equalFirstBlockGLBorel equalFirstBlockGLMeasurable equalFirstBlockLocalField equalFirstBlockLowerMeasurable equalFirstBlockLowerSeries equalFirstBlockMeasurable equalFirstBlockQuotientMeasurable equalFirstBlockSecondCountable equalFirstBlockTopology equalFirstBlockUnipotentBorel equalFirstBlockUnipotentMeasurable equalFirstBlockValuation equalLowerFourierCoefficientLaw equalLowerGroupIntegrand_reversedDual equalLowerIntegrand_reversedDual equalSecondBlockBorel equalSecondBlockGLBorel equalSecondBlockGLMeasurable equalSecondBlockLocalField equalSecondBlockMeasurable equalSecondBlockQuotientMeasurable equalSecondBlockSecondCountable equalSecondBlockTopology equalSecondBlockUnipotentBorel equalSecondBlockUnipotentMeasurable equalSecondBlockValuation exists_equalFirstBlockBound_forOrdinaryFunctional exists_equalFirstBlockCoefficientLaw exists_equalTwoSidedFirstBlockLaws exists_reversedEqualFirstBlockBound exists_strictFirstBlockBound_forOrdinaryFunctional exists_strictFirstBlockCoefficientLaw instBorelSpaceCarrier instMeasurableSpaceCarrier instTopologicalSpaceCarrier lowerInduced_inverseWhittakerType negatedSelfDualHaar negatedSelfDualHaar_val radicalAverage_eq_equalRankIntegrand reversedDualBlocks_whittakerType reversedDualSectionEquiv_ordinary reversedDual_oppositeTwistBlocks secondDual_oppositeTwistFunctional_val strictCoefficientBorel strictCoefficientMeasurable strictCoefficientQuotientMeasurable strictCoefficientSecondCountable strictCoefficientTopology strictDualSliceCoefficient strictDualSliceCoefficient_lowerSupport strictFirstBlockGLBorel strictFirstBlockGLMeasurable strictFirstBlockLocalField strictFirstBlockLowerMeasurable strictFirstBlockQuotientMeasurable strictFirstBlockTopology strictFirstBlockUnipotentBorel strictFirstBlockUnipotentMeasurable strictFirstBlockValuation strictNumeratorGLBorel strictNumeratorGLMeasurable strictNumeratorGLTopology strictNumeratorLocalField strictNumeratorLowerMeasurable strictNumeratorMeasurable strictNumeratorQuotientMeasurable strictNumeratorTopology strictNumeratorUnipotentBorel strictNumeratorUnipotentMeasurable strictNumeratorValuation strictRectangleMeasure strictResidueCardinalityUnit strictSliceCoefficient strictSliceCoefficient_lowerSupport twoBlock_strictInducedCoefficient_numerators unequalRankSliceCoefficient_lowerSupport unfoldedJacquetSeries unfoldedJacquetSeries_eq
open Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFrobeniusStatement EqualRankFunctionalEquationStatement EqualRankLastRowReductionStatement EqualRankNormalizedCompactIntegrationStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement EqualRankTrilinearUniquenessStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement LowerFirstBlockIntegrationInputStatement LowerFirstBlockSliceTowerInputStatement NormalizedProductWhittakerTypeStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement SliceIntegrable SliceIntegrableAt TwoBlockDominantFirstBlockLaurentIdentityStatement TwoBlockDualSectionJacquetStatement TwoBlockFirstBlockLaurentIdentityStatement TwoBlockFirstBlockQuotientIntegrationStatement TwoBlockFixedSliceUnfoldingStatement TwoBlockJacquetConvergenceStatement TwoBlockLowerFirstBlockQuotientIntegrationStatement TwoBlockLowerFixedSliceConvergenceStatement TwoBlockOrdinaryJacquetFunctionalStatement TwoBlockUnipotentQuotientIntegrationStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankPure_hasCompactSupport assembleLowerFirstBlockQuotientIntegration continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankContinuedForms equalRankFrobenius equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankLastRowReduction equalRankNormalizedCompactIntegration equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound finiteFunctionMellin finiteFunctionShellSeries hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit lowerFirstBlockIntegrationInput_of_sliceTower lowerFirstBlockSliceTowerInput measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductWhittakerType oneVariableMellin padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType padic_quotient_sigmaFinite padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice quotientIwasawaIntegration quotientRootIntegration rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight setIntegral_equalRankIntegrand_determinantSlice setIntegral_unequalRankAverage_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrableAt_unequalRankAverage_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockDualSectionJacquet twoBlockFirstBlockLaurentIdentity twoBlockFirstBlockQuotientIntegration twoBlockFixedSliceUnfolding twoBlockJacquetConvergence twoBlockLowerFirstBlockQuotientIntegration twoBlockLowerFixedSliceConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val twoBlockOrdinaryJacquetFunctional twoBlockUnipotentQuotientIntegration unequalRankAnalytic unequalRankAverage unequalRankAverage_eq_mul_spectralPoint_zpow unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankFunctionalEquation unequalRankGammaPropagation unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankIwasawaSupport unequalRankSliceCoefficient unequalRankSliceExpansion unequalRankSliceExpansion_of_converges unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unequalSliceMatrixMeasurable unequalSliceQuotientBorel unequalSliceQuotientMeasurable unequalSliceTopology whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory LaurentPolynomial
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement TwoBlockRowFourierCompanionStatement exists_rowSchwartz_order_lower_bound padicLatticeGeometry padicMatrixFourierSlice padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists padicUnipotentHaar_iota_fourier_duality_right twoBlockRowFourierCompanion
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CompactLocalizationStatement MirabolicCompactTwistedPairingStatement MirabolicFiniteLengthStatement MirabolicFunctionalMultiplicityStatement MirabolicTwistedPairingRigidityStatement MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier UnipotentOrbitStatement compactLocalization exchangedParabolic functionalsCongr hasCompactSupport_twoBlockCellRestriction inducedLocalization_of_prerequisites mirabolicCompactTwistedPairing mirabolicFiniteLength mirabolicFunctionalMultiplicity mirabolicUnitTest modelKirillovTransfer mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentOrbit unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {t r : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

local instance strictFirstBlockT2 : T2Space F :=
  (⟨⟩ : LocalFieldData F).fieldT2
local instance strictFirstBlockSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance strictFirstBlockMeasurable : MeasurableSpace F := borel _
local instance strictFirstBlockBorel : BorelSpace F := ⟨rfl⟩
local instance strictFirstBlockGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance strictFirstBlockGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance strictFirstBlockUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance strictFirstBlockUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
local instance strictFirstBlockQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F) := borel _
local instance strictFirstBlockQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
local instance strictFirstBlockLowerMeasurable :
    MeasurableSpace (TwoBlockLowerUnipotentQuotient.LowerQuotient h F) :=
  borel _
local instance strictFirstBlockLowerBorel :
    BorelSpace (TwoBlockLowerUnipotentQuotient.LowerQuotient h F) := ⟨rfl⟩

local notation "qF" => (Langlands.LocalFieldData.residueCardinality (⟨⟩ : LocalFieldData F))
local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

variable (htr : t < r)
  (ψ : UnitaryAdditiveCharacter F)
  (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (r + 1) F) V)
  (lambda : glFunctionals ψ r π)
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
  (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))

/-- Retained complete first-block witnesses at a strictly dominant test rank. -/
def StrictFirstBlockFactorCertificate
    (μA : Measure (LeftUnipotentQuotient (m 0) F))
    (ζ c : ℂˣ) (d : ℤ) (P Pdual : Polynomial ℂ) : Prop :=
  UnequalRankEpsilonEquation (lt_trans (firstBlock_lt_total h) htr) qF ψ abv μA ν.val
    π (σ 0) lambda (ell 0) c d ∧
  HasModelMinusOneScalar (σ 0) (ell 0) ζ ∧
  ∀ (j k : ℕ) (hr : r = m 0 + (j + k + 1)),
    IsNormalizedGenerator
      (unequalRankValuesAt j k hr qF ψ abv μA
        (rectangularMeasure ν.val j (m 0 + 1)) π (σ 0) lambda (ell 0)) P ∧
    IsNormalizedGenerator
      (dualUnequalRankRationalValuesAt (lt_trans (firstBlock_lt_total h) htr) j k hr
        qF ψ abv μA ν.val π (σ 0) lambda (ell 0)) Pdual

variable (J : glInverseFunctionals ψ t (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ))
  (μN : Measure (LeftUnipotentQuotient t F))
  (μA : Measure (LeftUnipotentQuotient (m 0) F))

/-- One retained epsilon monomial and normalized polynomial pair work for
all complementary rows, sections and actual large-model coefficients. -/
def StrictFirstBlockCoefficientLaw : Prop :=
  ∃ (ζ c : ℂˣ) (d : ℤ) (P Pdual : Polynomial ℂ),
    StrictFirstBlockFactorCertificate F h htr ψ ν π lambda σ ell μA ζ c d P Pdual ∧
    ∀ (j k : ℕ) (hr : r = t + (j + k + 1))
      (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σ)
      (Wtest : (coefficientModel π lambda).toSubmodule),
      let a := strictSliceCoefficient F hr ψ μN ν.val Wtest.val
        (modelMap (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) J f).val
      let b : BilateralLaurentSeries :=
        Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.kernelSliceCoefficient ν.val ell f Wtest.val μN hr
      Polynomial.eval₂ C (C ((qF : ℂ)⁻¹) * T (-1)) Pdual • b =
        (C ((ζ : ℂ) ^ r * (c : ℂ)) * T d * P.toLaurent) • a

omit σ ell J μN μA in
/-- The independently owned closed first-block result supplies a common bound
for any functional realizing the same actual ordinary Jacquet integral. -/
theorem exists_strictFirstBlockBound_forOrdinaryFunctional
    (H : TwoBlockDominantFirstBlockLaurentIdentityStatement.{uF,uV,uW})
    [Measure.IsMulRightInvariant (unipotentHaar F t)]
    [Measure.IsMulRightInvariant (unipotentHaar F (m 0))]
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hlambda : lambda.val ≠ 0)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell0 : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (hell0 : ∀ i, (ell0 i).val ≠ 0) :
    ∃ Cbound : ℝ, ∀ u : ℝ, Cbound < u →
      ∀ (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)),
        σ = twoBlockOppositeTwistBlocks F m τ u →
      ∀ (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i)),
        (∀ i, (ell i).val = (ell0 i).val) →
      ∀ (J : glInverseFunctionals ψ t (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ)),
        (∀ (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σ)
          (g : GeneralLinear (t + 1) F),
          J.val (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ g f) =
            Langlands.AllField.RankinSelberg.TwoBlockJacquet.jacquetFunction ψ (fun i => (ell i).val)
              (rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)) f g) →
      ∀ (μN : Measure (LeftUnipotentQuotient t F))
        (μA : Measure (LeftUnipotentQuotient (m 0) F)),
        IsCompatible (upperUnipotent (t + 1) F)
          (generalLinearHaar F t) (unipotentHaar F t) μN →
        IsCompatible (upperUnipotent (m 0 + 1) F)
          (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) μA →
        StrictFirstBlockCoefficientLaw F h htr ψ ν π lambda σ ell J μN μA := by
  obtain ⟨Cbound, hC⟩ := (H F ψ ν t r m h htr).2 π hπ lambda τ hτ ell0
  refine ⟨Cbound, fun u hu σ hσ ell hell J hJ μN μA hμN hμA => ?_⟩
  subst σ
  have hellEq : ell = fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i) := by
    funext i
    exact Subtype.ext (hell i)
  subst ell
  obtain ⟨-, J₀, -, hJ₀, hBody⟩ := hC u hu
  have hJEq : J = J₀ := by
    apply Subtype.ext
    ext f
    have he := (hJ f 1).trans (hJ₀ f 1).symm
    simpa only [map_one, Module.End.one_apply] using he
  subst J₀
  obtain ⟨-, -, -, -, hLaurent⟩ := hBody inferInstance inferInstance μN μA hμN hμA
  let σu := twoBlockOppositeTwistBlocks F m τ u
  let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i)
  have hσ0 : IsOfWhittakerType (m 0) (inverseStandardCharacter ψ (m 0)) (σu 0) :=
    (twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u 0 _).mpr
      ((isOfWhittakerType_standard_iff_inverse ψ (τ 0)).mp (hτ 0))
  have hEq := unequalRankFunctionalEquation F (⟨⟩ : LocalFieldData F) (m 0) r
    (lt_trans (firstBlock_lt_total h) htr) ψ μA hμA ν.val ν.property V (W 0) π (σu 0)
    hπ hσ0 lambda (ellu 0) hlambda (hell0 0)
  obtain ⟨c, d, hε⟩ := exists_unequalRankEpsilonEquation_iff.mpr hEq
  obtain ⟨ζ, P, Pdual, hζ, hgen, hLaw⟩ := hLaurent c d hε
  refine ⟨ζ, c, d, P, Pdual, ⟨hε, hζ,
    fun j k hr => ⟨(hgen j k hr).1, (hgen j k hr).2.1⟩⟩, ?_⟩
  intro j k hr f Wtest
  exact hLaw j k hr f Wtest

omit σ ell J μN μA in
set_option maxHeartbeats 1600000 in
/-- A common bound supplies a nonzero ordinary functional and its strict
first-block law, conditional on the independently owned analytic theorem. -/
theorem exists_strictFirstBlockCoefficientLaw
    (H : TwoBlockDominantFirstBlockLaurentIdentityStatement.{uF,uV,uW})
    [Measure.IsMulRightInvariant (unipotentHaar F t)]
    [Measure.IsMulRightInvariant (unipotentHaar F (m 0))]
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hlambda : lambda.val ≠ 0)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell0 : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (hell0 : ∀ i, (ell0 i).val ≠ 0) :
    ∃ Cbound : ℝ, ∀ u : ℝ, Cbound < u →
      let σu := twoBlockOppositeTwistBlocks F m τ u
      let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i)
      let μR := rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)
      (∀ f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σu,
        Langlands.AllField.RankinSelberg.TwoBlockJacquet.IsAbsIntegrable ψ (fun i => (ell0 i).val) μR f) ∧
      ∃ Ju : glInverseFunctionals ψ t (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σu),
        Ju.val ≠ 0 ∧
        (∀ (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σu)
          (g : GeneralLinear (t + 1) F),
          Ju.val (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σu g f) =
            Langlands.AllField.RankinSelberg.TwoBlockJacquet.jacquetFunction ψ (fun i => (ellu i).val) μR f g) ∧
        ∀ (μN : Measure (LeftUnipotentQuotient t F))
          (μA : Measure (LeftUnipotentQuotient (m 0) F)),
          IsCompatible (upperUnipotent (t + 1) F)
            (generalLinearHaar F t) (unipotentHaar F t) μN →
          IsCompatible (upperUnipotent (m 0 + 1) F)
            (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) μA →
          StrictFirstBlockCoefficientLaw F h htr ψ ν π lambda σu ellu Ju μN μA := by
  obtain ⟨Cfirst, hFirst⟩ := exists_strictFirstBlockBound_forOrdinaryFunctional
    F h htr ψ ν π lambda H hπ hlambda τ hτ ell0 hell0
  obtain ⟨Cjac, hJac⟩ := twoBlockOrdinaryJacquetFunctional F ψ ν t m h τ hτ ell0 hell0
  refine ⟨max Cfirst Cjac, fun u hu => ?_⟩
  dsimp only
  obtain ⟨habs, J, hJ0, hJ⟩ := hJac u (lt_of_le_of_lt (le_max_right _ _) hu)
  refine ⟨habs, J, hJ0, hJ, ?_⟩
  intro μN μA hμN hμA
  exact hFirst u (lt_of_le_of_lt (le_max_left _ _) hu)
    (twoBlockOppositeTwistBlocks F m τ u) rfl
    (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i))
    (fun _ => rfl) J hJ μN μA hμN hμA

end Langlands.AllField.RankinSelberg.DominantRankTransport
