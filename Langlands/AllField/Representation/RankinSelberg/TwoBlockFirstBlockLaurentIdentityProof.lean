import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentIdentityProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentAdapters
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentIdentityStatement
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentPointwise
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockQuotientIntegrationProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFixedSliceUnfoldingProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientIntegrationProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFixedSliceConvergenceProof
/-! # The polynomial-cleared first-block JPSS Laurent identity -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankLastRowReductionStatement EqualRankNormalizedCompactIntegrationStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement LowerFirstBlockIntegrationInputStatement LowerFirstBlockSliceTowerInputStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement SliceIntegrable SliceIntegrableAt TwoBlockFirstBlockLaurentIdentityStatement TwoBlockFirstBlockQuotientIntegrationStatement TwoBlockFixedSliceUnfoldingStatement TwoBlockJacquetConvergenceStatement TwoBlockLowerFirstBlockQuotientIntegrationStatement TwoBlockLowerFixedSliceConvergenceStatement TwoBlockUnipotentQuotientIntegrationStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement assembleLowerFirstBlockQuotientIntegration continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankLastRowReduction equalRankNormalizedCompactIntegration equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound finiteFunctionMellin finiteFunctionShellSeries hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit lowerFirstBlockIntegrationInput_of_sliceTower lowerFirstBlockSliceTowerInput measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow oneVariableMellin pairwise_disjoint_determinantSlice quotientIwasawaIntegration quotientRootIntegration rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockFirstBlockLaurentIdentity twoBlockFirstBlockQuotientIntegration twoBlockFixedSliceUnfolding twoBlockJacquetConvergence twoBlockLowerFirstBlockQuotientIntegration twoBlockLowerFixedSliceConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val twoBlockUnipotentQuotientIntegration unequalRankAnalytic unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIwasawaSupport unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement exists_rowSchwartz_order_lower_bound padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicScalarHaarScaling padicUnipotentHaar_iota_fourier_duality_right
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest modelKirillovTransfer mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration
open scoped ENNReal

universe uF uV uW

theorem twoBlockFirstBlockLaurentIdentity :
    TwoBlockFirstBlockLaurentIdentityStatement.{uF,uV,uW} := by
  intro F _ _ _ _ T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  intro ψ ν t m h hlt
  let := T.generalLinearTopologicalGroup (t + 1)
  let := T.generalLinearTopologicalGroup (m 0 + 1)
  intro G N GA NA NQ AQ HQ LQ
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : MeasurableSpace N := borel N
  let : BorelSpace N := ⟨rfl⟩
  let : MeasurableSpace GA := borel GA
  let : BorelSpace GA := ⟨rfl⟩
  let : MeasurableSpace NA := borel NA
  let : BorelSpace NA := ⟨rfl⟩
  let : MeasurableSpace NQ := borel NQ
  let : BorelSpace NQ := ⟨rfl⟩
  let : MeasurableSpace AQ := borel AQ
  let : BorelSpace AQ := ⟨rfl⟩
  let : MeasurableSpace HQ := borel HQ
  let : BorelSpace HQ := ⟨rfl⟩
  let : MeasurableSpace LQ := borel LQ
  let : BorelSpace LQ := ⟨rfl⟩
  intro μG μN μGA μNA μR q abv
  obtain ⟨_, _, hN, _, hexN, hexH, hfixed⟩ :=
    twoBlockFixedSliceUnfolding.{uF,uV,uW} F ψ ν t m h
  obtain ⟨_, _, hsigma, hlower⟩ :=
    twoBlockLowerFixedSliceConvergence.{uF,uV,uW} F ψ ν t m h
  obtain ⟨_, _, hslices, _, _, _, _, _, _, _, _, _, _, _, _, μA0, _, _, hA0map, _, _, μL, _,
      _, _, _, _, hNa, _, _, _, _, _, _, hexA, hexM, hexL, _, hcube, hmain⟩ :=
    twoBlockLowerFirstBlockQuotientIntegration.{uF} F t m h
  refine ⟨hN, hNa, hexN, hexA, ?_⟩
  intro V _ _ π hπ lambda W _ _ τ hτ ell
  obtain ⟨C₁, hC₁⟩ := hfixed τ hτ ell
  obtain ⟨C₂, hC₂⟩ := hlower π hπ lambda τ hτ ell
  refine ⟨max C₁ C₂, ?_⟩
  intro u hu σu ellu νN νA hνN hνA νMinus
  have hu₁ : C₁ < u := lt_of_le_of_lt (le_max_left _ _) hu
  have hu₂ : C₂ < u := lt_of_le_of_lt (le_max_right _ _) hu
  obtain ⟨hνNσ, hνMinusσ⟩ := hsigma νN hνN
  obtain ⟨νM, hνM⟩ := hexM
  obtain ⟨νL, hνL⟩ := hexL
  have hνAσ : SigmaFinite νA := (hmain νA νM νL νN hνA hνM hνL hνN).1
  refine ⟨hνNσ, hνAσ, hνMinusσ, ?_, ?_⟩
  · intro f Wtest Φ Eup Aup Elow
    obtain ⟨νH, hνH⟩ := hexH
    have hup := fun k : ℤ => hC₁ u hu₁ f V π hπ.1.1 lambda Wtest Φ k
    have hlow := fun k : ℤ => hC₂ u hu₂ νN hνN f Wtest Φ k
    refine ⟨(hup 0).2.1, (hlow 0).1, fun k => ⟨?_, (hlow k).2.1⟩⟩
    exact ((hup k).2.2.2.2.2 νN νH hνN hνH).2.2.1
  · intro cε d hε
    obtain ⟨ζ, P, Pdual, hζ, hbody⟩ := hε
    refine ⟨ζ, P, Pdual, hζ, hbody, ?_⟩
    intro f Wtest Φ Eup Aup Elow Zup Zlow D
    have hr0 : t = m 0 + (m 1 + 0 + 1) := by
      have := TwoBlockJacquet.blockRanks_add h
      omega
    obtain ⟨hP, hPd, hpairs⟩ := hbody (m 1) 0 hr0
    by_cases hdeg : lambda.val = 0 ∨ (ellu 0).val = 0
    · have hE0 : Eup = 0 := by
        rcases hdeg with h0 | h0
        · exact Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.upperIntegrand_eq_zero_of_test ellu f Wtest.val
            (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.coefficientModel_val_eq_zero h0 Wtest) Φ
        · exact Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.upperIntegrand_eq_zero_of_first ellu h0 f Wtest.val Φ
      have hL0 : Elow = 0 := by
        rcases hdeg with h0 | h0
        · exact Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.lowerIntegrand_eq_zero_of_test ellu f Wtest.val
            (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.coefficientModel_val_eq_zero h0 Wtest) Φ ν.val
        · exact Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.lowerIntegrand_eq_zero_of_first ellu h0 f Wtest.val
            Φ ν.val
      have hA0 : Aup = 0 := by
        funext z
        induction z using Quotient.inductionOn with
        | h g =>
          change (∫ x, Eup (TwoBlockUnipotentQuotient.fiberPoint h F x g) ∂μR) = 0
          rw [hE0]
          simp
      have hZup : Zup = 0 := by
        funext k
        change (∫ z, Aup z ∂νN.restrict (determinantSlice T t k)) = (0 : ℂ)
        rw [hA0]
        simp
      have hZlow : Zlow = 0 := by
        funext k
        change (∫ z, Elow z ∂νMinus.restrict
          (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k)) = (0 : ℂ)
        rw [hL0]
        simp
      rw [hZup, hZlow, smul_zero, smul_zero]
    rw [not_or] at hdeg
    obtain ⟨hlam, hell⟩ := hdeg
    let MQ := Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.MixedQuotient F h
    let LQ' := Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.LowerMixedQuotient F h
    let : MeasurableSpace MQ := borel MQ
    let : BorelSpace MQ := ⟨rfl⟩
    let : MeasurableSpace LQ' := borel LQ'
    let : BorelSpace LQ' := ⟨rfl⟩
    obtain ⟨_, _, μA0', _, _, hA0'map, _, _, _, _, _, _, _, _, hmainU⟩ :=
      twoBlockFirstBlockQuotientIntegration.{uF} F t m h
    have hA0eq : μA0' = μA0 := by
      let A0 := Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.normOneSubgroup F (m 0 + 1)
      let : MeasurableSpace A0 := borel A0
      let : BorelSpace A0 := ⟨rfl⟩
      have he := (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.isOpenEmbedding_normOneSubtype F
        (m 0 + 1)).measurableEmbedding
      rw [← he.comap_map μA0', ← he.comap_map μA0, hA0'map, hA0map]
    subst hA0eq
    obtain ⟨νH, hνH⟩ := hexH
    obtain ⟨_, _, _, hupk⟩ := hmainU νA νH νM hνA hνH hνM
    obtain ⟨_, _, _, _, _, _, hrad, hlowk⟩ := hmain νA νM νL νN hνA hνM hνL hνN
    let μR' := rectangularMeasure ν.val (m 1 + 1) (m 0 + 1)
    obtain ⟨κR, _, hκR, _, hlintR, hlawR⟩ := hrad μR'
    have := Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν.val
    let hInv := Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.normOneRightInvariant_of_isCompatible F (m 0)
      μGA μNA νA hνA
    let fk : ℤ → MQ → ℂ := fun k =>
      Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.firstBlockAverage F h νA hInv k Eup
    let Uk : ℤ → LQ' → ℂ := fun k =>
      Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.radicalAverage F h μR' (fk k)
    let Lk : ℤ → LQ' → ℂ := fun k =>
      Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.firstBlockAverage F h νA hInv k Elow
    let νL0' := νL.restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.determinantSlice F h 0)
    have hW : Continuous Wtest.val.val := glModelFunction_continuous ψ t π hπ.1.1 lambda Wtest
    have hEc : Continuous Eup :=
      Langlands.AllField.RankinSelberg.TwoBlockUnfolding.integrand_continuous ψ ellu f Wtest.val Φ hW
    have hEm : Measurable Eup := hEc.measurable
    have hElm : Measurable Elow := (hC₂ u hu₂ νN hνN f Wtest Φ 0).1
    have hc := TwoBlockFirstBlockLaurent.rectangularMeasure_integer_cube_swap ν.val
      (m 0 + 1) (m 1 + 1)
    have hZup : ∀ k : ℤ, Integrable (Uk k) νL0' ∧ Zup k = ∫ z, Uk k z ∂νL0' := by
      intro k
      obtain ⟨κ, _, hκ, _, _, hlaw⟩ := hupk k
      have hfixk := (hC₁ u hu₁ f V π hπ.1.1 lambda Wtest Φ k).2.2.2.2.2 νN νH hνN hνH
      obtain ⟨hfki, hEeq⟩ := (hlaw Eup hEm).2 hfixk.1
      have hfkm : Measurable (fk k) := by
        have hfk := Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.firstBlockAverage_eq_integral_kernel F h νA hInv k
          κ hκ Eup hEm
        change Measurable (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.firstBlockAverage F h νA hInv k Eup)
        rw [hfk]
        exact (hEm.stronglyMeasurable.integral_kernel (κ := κ)).measurable
      obtain ⟨_, hUi, hUeq⟩ := (hlawR (fk k) hfkm).2 hfki
      refine ⟨hUi, ?_⟩
      have hEeq' : (∫ z in TwoBlockUnipotentQuotient.projection h F ⁻¹'
          Langlands.AllField.RankinSelberg.determinantSlice T t k, Eup z ∂νH) = _ := hEeq
      change (∫ z, Aup z ∂νN.restrict (determinantSlice T t k)) = _
      rw [hfixk.2.2.2, hEeq', hUeq, hc]
    have hZlow : ∀ k : ℤ, Integrable (Lk k) νL0' ∧
        Zlow k = ∫ z, (q : ℂ) ^ (-(k * ((m 1 + 1 : ℕ) : ℤ))) * Lk k z ∂νL0' := by
      intro k
      obtain ⟨_, _, _, κA, _, _, _, _, hlawA⟩ := hlowk k
      obtain ⟨_, hLi, hLeq⟩ := (hlawA Elow hElm).2 (hC₂ u hu₂ νN hνN f Wtest Φ k).2.1
      refine ⟨hLi, ?_⟩
      change (∫ z, Elow z ∂νMinus.restrict
        (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k)) = _
      rw [hLeq, integral_const_mul, ENNReal.toReal_ofReal (zpow_nonneg (Nat.cast_nonneg _) _),
        Complex.real_smul]
      push_cast
      rfl
    have hfin : ∀ k : ℤ, ∀ᵐ z ∂νL0', ∀ g : G, z = Quotient.mk _ g →
        (∫⁻ Z, ∫⁻ x, ‖Eup (TwoBlockFirstBlockQuotient.fiberPoint h F x
            (TwoBlockLowerUnipotentQuotient.lowerRadical h F Z * g))‖ₑ
          ∂νA.restrict (determinantSlice T (m 0) k) ∂μR') ≠ ⊤ := by
      intro k
      obtain ⟨κ, _, hκ, _, hlint, _⟩ := hupk k
      have hfixk := (hC₁ u hu₁ f V π hπ.1.1 lambda Wtest Φ k).2.2.2.2.2 νN νH hνN hνH
      obtain ⟨hc0', hctop', -⟩ := hcube μR'
      have hae := TwoBlockFirstBlockLaurent.ae_lintegral_kernel_comp_lt_top νL0'
        (νM.restrict (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.determinantSlice F h 0))
        (νH.restrict (Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.determinantSlice F h k)) κR κ _ hctop'.ne
        hlintR hlint Eup hEm hfixk.1
      filter_upwards [hae] with z hz g hzg
      subst hzg
      have hF : Measurable fun y => ∫⁻ w, ‖Eup w‖ₑ ∂κ y := hEm.enorm.lintegral_kernel
      have hrm : Measurable fun Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F =>
          Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.radicalFiberPoint F h Z g :=
        (Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.continuous_radicalFiberPoint F h).comp
          (continuous_id.prodMk continuous_const) |>.measurable
      rw [hκR g, lintegral_map hF hrm] at hz
      refine ne_of_lt (lt_of_eq_of_lt ?_ hz)
      refine lintegral_congr fun Z => ?_
      change _ = ∫⁻ w, ‖Eup w‖ₑ ∂κ (Quotient.mk _
        (TwoBlockLowerUnipotentQuotient.lowerRadical h F Z * g))
      have hfm : Measurable fun x : AQ => TwoBlockFirstBlockQuotient.fiberPoint h F x
          (TwoBlockLowerUnipotentQuotient.lowerRadical h F Z * g) :=
        ((Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.continuous_fiberPoint F h).comp
          (continuous_id.prodMk continuous_const)).measurable
      rw [hκ, lintegral_map hEm.enorm hfm]
    have hσ : IsOfWhittakerType (m 0) (inverseStandardCharacter ψ (m 0)) (σu 0) :=
      (twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u 0
        (inverseStandardCharacter ψ (m 0))).mpr
        ((isOfWhittakerType_standard_iff_inverse ψ (τ 0)).mp (hτ 0))
    obtain ⟨Kf, hKf, hKle, hKm⟩ : ∃ Kf : (Fin (m 0 + 1) → F) → AQ → ℂ,
        (∀ x v, Kf x (Quotient.mk _ v) = ψ.complex (Matrix.vecMul x (v⁻¹).val 0)) ∧
        (∀ x q, ‖Kf x q‖ ≤ 1) ∧
        ∀ k : ℤ, AEStronglyMeasurable (Function.uncurry Kf)
          ((rowMeasure ν.val (m 0 + 1)).prod (νA.restrict (determinantSlice T (m 0) k))) :=
      ⟨Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.firstRowCharacter ψ (m 0), fun x v => rfl,
        fun x q => (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.norm_firstRowCharacter ψ (m 0) x q).le,
        fun k => Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.aestronglyMeasurable_firstRowCharacter ψ (m 0) _⟩
    have hH : ∀ (g : G) (k : ℤ), AEStronglyMeasurable
        (Function.uncurry fun Z x => Eup (TwoBlockFirstBlockQuotient.fiberPoint h F x
          (TwoBlockLowerUnipotentQuotient.lowerRadical h F Z * g)))
        (μR'.prod (νA.restrict (determinantSlice T (m 0) k))) := fun g k =>
      Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.aestronglyMeasurable_comp_fiberPoint_lowerRadical h Eup g hEc _
    let Sser : LQ' → BilateralLaurentSeries := fun z k =>
      (q : ℂ) ^ (-(k * ((m 1 + 1 : ℕ) : ℤ))) * Lk k z
    let User : LQ' → BilateralLaurentSeries := fun z k => Uk k z
    have hZlowEq : Zlow = BilateralLaurentSeries.coeffwiseIntegral νL0' Sser :=
      funext fun k => (hZlow k).2
    have hZupEq : Zup = BilateralLaurentSeries.coeffwiseIntegral νL0' User :=
      funext fun k => (hZup k).2
    rw [hZlowEq, hZupEq]
    refine TwoBlockFirstBlockLaurent.integral_laurent_identity_ae D _
      (fun k => (hZlow k).1.const_mul _) (fun k => (hZup k).1) ?_
    filter_upwards [ae_all_iff.mpr hfin] with z hz
    induction z using Quotient.inductionOn with
    | h g =>
      exact Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.pointwise_laurent_identity hlt hr0 π lambda ellu f Wtest Φ
        Kf νA hνA ν.val ζ cε d P Pdual hπ hσ hlam hell hP hPd hpairs g hKf hKle hKm (hH g)
        (fun k => hz k g rfl)

end Langlands.AllField.RankinSelberg
