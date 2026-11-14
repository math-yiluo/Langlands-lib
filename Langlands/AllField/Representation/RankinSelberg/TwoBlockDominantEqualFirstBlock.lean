import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualFirstBlock
import Langlands.AllField.Representation.RankinSelberg.EqualRankContinuedFormsProofSupplement
import Langlands.AllField.Representation.RankinSelberg.EqualRankFrobeniusProof
import Langlands.AllField.Representation.RankinSelberg.GammaFromWhittakerType
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantJacquetSeries
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentIdentityProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankFunctionalEquationProof
import Langlands.AllField.Representation.Whittaker.MirabolicCompactTwistedPairingProofSupplement
import Langlands.AllField.Representation.Whittaker.MirabolicPairingRigidityStepSupplement
/-!
# First-block Laurent laws for actual equal-rank Jacquet coefficients

The ordinary Jacquet realization and the published first-block theorem supply
the actual law at all sufficiently large real deformation parameters.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg.DominantRankTransport hiding EqualFirstBlockCoefficientLaw equalFirstBlockBorel equalFirstBlockGLBorel equalFirstBlockGLMeasurable equalFirstBlockLocalField equalFirstBlockLowerMeasurable equalFirstBlockLowerSeries equalFirstBlockMeasurable equalFirstBlockQuotientMeasurable equalFirstBlockSecondCountable equalFirstBlockTopology equalFirstBlockUnipotentBorel equalFirstBlockUnipotentMeasurable equalFirstBlockValuation exists_equalFirstBlockCoefficientLaw instBorelSpaceCarrier instMeasurableSpaceCarrier instTopologicalSpaceCarrier lowerInduced_inverseWhittakerType radicalAverage_eq_equalRankIntegrand unfoldedJacquetSeries unfoldedJacquetSeries_eq
open Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFrobeniusStatement EqualRankFunctionalEquationStatement EqualRankLastRowReductionStatement EqualRankNormalizedCompactIntegrationStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement EqualRankTrilinearUniquenessStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement LowerFirstBlockIntegrationInputStatement LowerFirstBlockSliceTowerInputStatement NormalizedProductWhittakerTypeStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement SliceIntegrable SliceIntegrableAt TwoBlockFirstBlockLaurentIdentityStatement TwoBlockFirstBlockQuotientIntegrationStatement TwoBlockFixedSliceUnfoldingStatement TwoBlockJacquetConvergenceStatement TwoBlockLowerFirstBlockQuotientIntegrationStatement TwoBlockLowerFixedSliceConvergenceStatement TwoBlockOrdinaryJacquetFunctionalStatement TwoBlockUnipotentQuotientIntegrationStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement assembleLowerFirstBlockQuotientIntegration continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankContinuedForms equalRankFrobenius equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankLastRowReduction equalRankNormalizedCompactIntegration equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound finiteFunctionMellin finiteFunctionShellSeries hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit lowerFirstBlockIntegrationInput_of_sliceTower lowerFirstBlockSliceTowerInput measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductWhittakerType oneVariableMellin padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType padic_quotient_sigmaFinite padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice quotientIwasawaIntegration quotientRootIntegration rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockFirstBlockLaurentIdentity twoBlockFirstBlockQuotientIntegration twoBlockFixedSliceUnfolding twoBlockJacquetConvergence twoBlockLowerFirstBlockQuotientIntegration twoBlockLowerFixedSliceConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val twoBlockOrdinaryJacquetFunctional twoBlockUnipotentQuotientIntegration unequalRankAnalytic unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankFunctionalEquation unequalRankGammaPropagation unequalRankIwasawaSupport unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory LaurentPolynomial
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement exists_rowSchwartz_order_lower_bound padicLatticeGeometry padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists padicUnipotentHaar_iota_fourier_duality_right
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CompactLocalizationStatement MirabolicCompactTwistedPairingStatement MirabolicFiniteLengthStatement MirabolicFunctionalMultiplicityStatement MirabolicTwistedPairingRigidityStatement MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier UnipotentOrbitStatement compactLocalization exchangedParabolic functionalsCongr hasCompactSupport_twoBlockCellRestriction inducedLocalization_of_prerequisites mirabolicCompactTwistedPairing mirabolicFiniteLength mirabolicFunctionalMultiplicity mirabolicUnitTest modelKirillovTransfer mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentOrbit unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

local instance equalFirstBlockT2 : T2Space F :=
  (⟨⟩ : LocalFieldData F).fieldT2
local instance equalFirstBlockSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance equalFirstBlockMeasurable : MeasurableSpace F := borel _
local instance equalFirstBlockBorel : BorelSpace F := ⟨rfl⟩
local instance equalFirstBlockGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance equalFirstBlockGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance equalFirstBlockUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance equalFirstBlockUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
local instance equalFirstBlockQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F) := borel _
local instance equalFirstBlockQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
local instance equalFirstBlockLowerMeasurable :
    MeasurableSpace (TwoBlockLowerUnipotentQuotient.LowerQuotient h F) :=
  borel _
local instance equalFirstBlockLowerBorel :
    BorelSpace (TwoBlockLowerUnipotentQuotient.LowerQuotient h F) := ⟨rfl⟩

local notation "qF" => (Langlands.LocalFieldData.residueCardinality (⟨⟩ : LocalFieldData F))
local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

variable (ψ : UnitaryAdditiveCharacter F)
  (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (t + 1) F) V)
  (lambda : glFunctionals ψ t π)
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
  (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
  (J : glInverseFunctionals ψ t (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ))
  (μN : Measure (LeftUnipotentQuotient t F))
  (μA : Measure (LeftUnipotentQuotient (m 0) F))

/-- The actual lower quotient coefficient series of the equal-rank
first-block unfolding, retaining both supplied measures. -/
def equalFirstBlockLowerSeries
    (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σ)
    (Wtest : (coefficientModel π lambda).toSubmodule)
    (Φ : SchwartzBruhat (Fin (t + 1) → F)) : BilateralLaurentSeries :=
  fun k => ∫ z, Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.integrand ell f Wtest.val Φ ν.val z
    ∂(Measure.map
      (TwoBlockLowerUnipotentQuotient.lowerToStandard h F).symm μN).restrict
        (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k)

/-- One epsilon monomial and one normalized polynomial pair, common to all
sections, model coefficients and row tests, give the actual first-block law. -/
def EqualFirstBlockCoefficientLaw : Prop :=
  ∃ (ζ c : ℂˣ) (d : ℤ) (P Pdual : Polynomial ℂ),
    UnequalRankEpsilonEquation (firstBlock_lt_total h) qF ψ abv μA ν.val
      π (σ 0) lambda (ell 0) c d ∧
    HasModelMinusOneScalar (σ 0) (ell 0) ζ ∧
    (∀ (j k : ℕ) (hr : t = m 0 + (j + k + 1)),
      IsNormalizedGenerator
        (unequalRankValuesAt j k hr qF ψ abv μA
          (rectangularMeasure ν.val j (m 0 + 1)) π (σ 0) lambda (ell 0)) P ∧
      IsNormalizedGenerator
        (dualUnequalRankRationalValuesAt (firstBlock_lt_total h) j k hr
          qF ψ abv μA ν.val π (σ 0) lambda (ell 0)) Pdual) ∧
    ∀ (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σ)
      (Wtest : (coefficientModel π lambda).toSubmodule)
      (Φ : SchwartzBruhat (Fin (t + 1) → F)),
      let a : BilateralLaurentSeries :=
        equalRankSliceCoefficient (⟨⟩ : LocalFieldData F) μN ψ Wtest.val
          (modelMap (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) J f).val Φ
      let b := equalFirstBlockLowerSeries F h ψ ν π lambda σ ell μN f Wtest Φ
      Polynomial.eval₂ C (C ((qF : ℂ)⁻¹) * T (-1)) Pdual • b =
        (C ((ζ : ℂ) ^ t * (c : ℂ)) * T d * P.toLaurent) • a

omit σ ell J μN μA in
/-- Genuine ordinary Jacquet functionals and the actual first-block Laurent
law exist above one bound, uniformly over both compatible quotient measures.
The small-pair epsilon equation is derived from the published theorem. -/
theorem exists_equalFirstBlockCoefficientLaw
    [Measure.IsMulRightInvariant (unipotentHaar F t)]
    [Measure.IsMulRightInvariant (unipotentHaar F (m 0))]
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
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
          EqualFirstBlockCoefficientLaw F h ψ ν π lambda σu ellu Ju μN μA := by
  obtain ⟨_, _, _, _, hFirst⟩ :=
    twoBlockFirstBlockLaurentIdentity.{uF,uV,uW} F ψ ν t m h
  obtain ⟨Cfirst, hCfirst⟩ := hFirst π hπ lambda τ hτ ell0
  obtain ⟨Cjac, hCjac⟩ := twoBlockOrdinaryJacquetFunctional F ψ ν t m h τ hτ ell0 hell0
  refine ⟨max Cfirst Cjac, fun u hu => ?_⟩
  let σu := twoBlockOppositeTwistBlocks F m τ u
  let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i)
  let μR := rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)
  obtain ⟨habs, Ju, hJu0, hJu⟩ := hCjac u (lt_of_le_of_lt (le_max_right _ _) hu)
  refine ⟨habs, Ju, hJu0, hJu, ?_⟩
  intro μN μA hμN hμA
  obtain ⟨_, _, _, _, hLaurent⟩ :=
    hCfirst u (lt_of_le_of_lt (le_max_left _ _) hu) μN μA hμN hμA
  have hσ0 : IsOfWhittakerType (m 0) (inverseStandardCharacter ψ (m 0)) (σu 0) :=
    (twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u 0 _).2
      ((isOfWhittakerType_standard_iff_inverse ψ (τ 0)).1 (hτ 0))
  have heq := unequalRankFunctionalEquation F (⟨⟩ : LocalFieldData F) (m 0) t
    (firstBlock_lt_total h) ψ μA hμA ν.val ν.property V (W 0) π (σu 0)
    hπ hσ0 lambda (ellu 0) hlambda (hell0 0)
  obtain ⟨c, d, hEpsilon⟩ := exists_unequalRankEpsilonEquation_iff.mpr heq
  obtain ⟨ζ, P, Pdual, hζ, hBody, hLaw⟩ := hLaurent c d hEpsilon
  refine ⟨ζ, c, d, P, Pdual, hEpsilon, hζ,
    fun j k hr => ⟨(hBody j k hr).1, (hBody j k hr).2.1⟩, ?_⟩
  intro f Wtest Φ
  have ha := hLaw f Wtest Φ
  change _ = _ at ha
  change _ = _
  rw [← unfoldedJacquetSeries_eq F h ψ σu ellu μR μN Ju hJu f Wtest.val Φ]
  exact ha

end Langlands.AllField.RankinSelberg.DominantRankTransport
