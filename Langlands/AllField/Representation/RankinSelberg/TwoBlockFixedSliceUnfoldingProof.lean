import Langlands.Representation.RankinSelberg.TwoBlockFixedSliceUnfoldingProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFixedSliceAnalysis
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFixedSliceUnfoldingStatement
import Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergenceProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockUnipotentQuotientIntegrationProof
import Langlands.AllField.Representation.RankinSelberg.WhittakerRowSliceCompactSupportProof
/-! # The actual fixed-slice first unfolding of JPSS Section 4.6 -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankLastRowReductionStatement EqualRankSliceSupportStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt TwoBlockFixedSliceUnfoldingStatement TwoBlockJacquetConvergenceStatement TwoBlockUnipotentQuotientIntegrationStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankLastRowReduction equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockFixedSliceUnfolding twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val twoBlockUnipotentQuotientIntegration whittakerRowSliceCompactSupport zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockUnipotentQuotient hiding FiberKernelSFiniteStatement analytic_of_comp_eq_smul continuous_fiberPoint continuous_projection determinantSlice fiberIntegral fiberIntegral_def fiberIntegral_upperUnipotent_mul fiberKernel fiberKernel_compact_ne_top fiberKernel_isSFinite fiberKernel_mk fiberMeasures_upperUnipotent_mul iUnion_determinantSlice integerCube_mass_pos_lt_top isClopen_determinantSlice map_unipotentShift measurableSet_determinantSlice measurable_fiberMeasures mem_determinantSlice mk_mem_determinantSlice pairwise_disjoint_determinantSlice radicalAverage radicalAverage_eq_integral_kernel radicalAverage_mk
open Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient hiding determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open scoped ENNReal

universe uF uV uW

/-- Absolute convergence and the normalized first unfolding on every determinant slice,
with the supplied self-dual rectangular measure and its integral-cube mass retained. -/
theorem twoBlockFixedSliceUnfolding :
    TwoBlockFixedSliceUnfoldingStatement.{uF,uV,uW} := by
  intro F _ _ _ _ T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  intro ψ ν t m h
  let := T.generalLinearTopologicalGroup (t + 1)
  let := T.generalLinearLocallyCompactSpace (t + 1)
  let := T.generalLinearSecondCountableTopology (t + 1)
  let G := GeneralLinear (t + 1) F
  let N := upperUnipotent (t + 1) F
  let H := blockUnipotent h F
  let NQ := LeftUnipotentQuotient t F
  let HQ := BlockQuotient h F
  let R := Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : MeasurableSpace N := borel N
  let : BorelSpace N := ⟨rfl⟩
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let : ∀ i : Fin 2, MeasurableSpace (upperUnipotent (m i + 1) F) :=
    fun i => borel (upperUnipotent (m i + 1) F)
  let : ∀ i : Fin 2, BorelSpace (upperUnipotent (m i + 1) F) :=
    fun _ => ⟨rfl⟩
  let : ∀ i : Fin 2, SecondCountableTopology (upperUnipotent (m i + 1) F) :=
    fun i => by
      let := T.generalLinearSecondCountableTopology (m i + 1)
      exact Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : BorelSpace (BlockUnipotents m F) := inferInstance
  let : BorelSpace R := inferInstance
  let : MeasurableSpace NQ := borel NQ
  let : BorelSpace NQ := ⟨rfl⟩
  let : MeasurableSpace HQ := borel HQ
  let : BorelSpace HQ := ⟨rfl⟩
  let μG : Measure G := generalLinearHaar F t
  let μN : Measure N := unipotentHaar F t
  let μH : Measure H := Measure.map (blockUnipotentEquiv h F)
    (Measure.pi (fun i : Fin 2 => unipotentHaar F (m i)))
  let μR : Measure R := rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)
  let c : ℝ≥0∞ := μR {x | ∀ a b, x a b ∈ (ValuativeRel.valuation F).integer}
  obtain ⟨hμH, hμHreg, hN, hH, hexN, hexH, htower⟩ :=
    twoBlockUnipotentQuotientIntegration F t m h
  let := hN
  let := hH
  obtain ⟨hc0, hc, κ, hκfin, hκ, htowerR⟩ := htower μR
  let := hκfin
  refine ⟨hc0, hc, hN, hH, hexN, hexH, ?_⟩
  intro W _ _ τ hτ ell
  obtain ⟨C, hC⟩ := Langlands.AllField.RankinSelberg.TwoBlockConvergence.exists_bound_isAbsIntegrable_of_factorization
    F h ψ ν.val τ hτ ell (Langlands.AllField.RankinSelberg.TwoBlockConvergence.exists_radical_factorization F h)
  refine ⟨C, ?_⟩
  intro u hu f V _ _ π hπ ℓ Wtest Φ k
  let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)
  let E : HQ → ℂ := Langlands.AllField.RankinSelberg.TwoBlockUnfolding.integrand ellu f Wtest.val Φ
  let slice : Set NQ := Langlands.AllField.RankinSelberg.determinantSlice T t k
  let Hslice : Set HQ := projection h F ⁻¹' slice
  let A : NQ → ℂ := radicalAverage F h μR E
  let Aabs : NQ → ℂ := radicalAverage F h μR (fun z => (‖E z‖ : ℂ))
  have hW : Continuous Wtest.val.val :=
    glModelFunction_continuous ψ t π hπ ℓ Wtest
  have hEc : Continuous E := Langlands.AllField.RankinSelberg.TwoBlockUnfolding.integrand_continuous ψ ellu f Wtest.val Φ hW
  obtain ⟨hAc, hAabsc⟩ :=
    Langlands.AllField.RankinSelberg.TwoBlockUnfolding.radicalAverages_continuous ψ ellu f Wtest.val Φ μR hW
  have hfiber : ∀ g : G, Integrable (fun x => E (fiberPoint h F x g)) μR := by
    intro g
    have hraw := hC u hu f g
    change Integrable (Langlands.AllField.RankinSelberg.TwoBlockJacquet.integrand ψ (fun i => (ell i).val) f g) μR at hraw
    simpa only [E, ellu, Langlands.AllField.RankinSelberg.TwoBlockUnfolding.integrand_fiberPoint,
      twoBlockOppositeTwistFunctional_val] using
      (hraw.const_mul (Wtest.val.val g)).mul_const (Φ (lastRow g))
  refine ⟨hEc.measurable, hAc.measurable, hAabsc.measurable, hfiber, ?_, ?_⟩
  · intro g
    exact Langlands.AllField.RankinSelberg.TwoBlockUnfolding.radicalAverage_integrand_mk ellu f Wtest.val Φ μR g
  · intro νN νH hνN hνH
    let := hνN.regular
    let := leftQuotient_locallyCompactSpace N
    let := Topology.IsOpenQuotientMap.secondCountableTopology
      (leftQuotient_isOpenQuotientMap N)
    have hslice : IsClopen slice := Langlands.AllField.RankinSelberg.isClopen_determinantSlice T t k
    have hrow := whittakerRowSliceCompactSupport F T t ψ V π hπ ℓ Wtest Φ k
    have habs_zero : ∀ q : NQ,
        whittakerNorm ψ Wtest.val q * ‖Φ (quotientLastRow t q)‖ = 0 → Aabs q = 0 := by
      intro q
      induction q using Quotient.inductionOn with
      | h g =>
        intro hz
        simp only [whittakerNorm_mk, quotientLastRow_mk] at hz
        change radicalAverage F h μR
          (fun z => (‖Langlands.AllField.RankinSelberg.TwoBlockUnfolding.integrand ellu f Wtest.val Φ z‖ : ℂ))
          (Quotient.mk _ g) = 0
        rw [Langlands.AllField.RankinSelberg.TwoBlockUnfolding.radicalAverage_norm_integrand_mk]
        rcases mul_eq_zero.mp hz with hw | hphi
        · simp only [hw, Complex.ofReal_zero, zero_mul]
        · simp only [hphi, Complex.ofReal_zero, mul_zero]
    have hcompact : HasCompactSupport (slice.indicator Aabs) := by
      apply hrow.mono
      intro q hq
      change slice.indicator Aabs q ≠ 0 at hq
      change slice.indicator
        (fun q => whittakerNorm ψ Wtest.val q * ‖Φ (quotientLastRow t q)‖) q ≠ 0
      intro hz
      by_cases hqs : q ∈ slice
      · rw [Set.indicator_of_mem hqs] at hq hz
        exact hq (habs_zero q hz)
      · simp only [Set.indicator_of_notMem hqs] at hq
        exact hq rfl
    have hAabsi : Integrable Aabs (νN.restrict slice) := by
      apply (integrable_indicator_iff hslice.isOpen.measurableSet).mp
      exact (hslice.continuous_indicator hAabsc).integrable_of_hasCompactSupport hcompact
    have hκfiber : ∀ q : NQ, Integrable E (κ q) := by
      intro q
      induction q using Quotient.inductionOn with
      | h g =>
        rw [hκ g]
        have hcont : Continuous (fun x : R => fiberPoint h F x g) :=
          continuous_quotient_mk'.comp
            ((TwoBlockJacquet.continuous_upperRadical h F).mul continuous_const)
        exact (integrable_map_measure hEc.aestronglyMeasurable
          hcont.measurable.aemeasurable).mpr (hfiber g)
    have habs_eq : Aabs = fun q => Complex.ofReal (∫ z, ‖E z‖ ∂κ q) := by
      simpa only [integral_complex_ofReal] using
        radicalAverage_eq_integral_kernel F h μR κ hκ
          (fun z => (‖E z‖ : ℂ)) (Complex.measurable_ofReal.comp hEc.measurable.norm)
    have hnorm : Integrable (fun q => ∫ z, ‖E z‖ ∂κ q) (νN.restrict slice) := by
      have hr := hAabsi.re
      change Integrable (fun q => (Aabs q).re) (νN.restrict slice) at hr
      rw [habs_eq] at hr
      exact hr
    obtain ⟨_, _, ht⟩ := htowerR νN νH hνN hνH
    have htE := (ht slice hslice.isOpen.measurableSet).2.2 E hEc.measurable
    have hEi : Integrable E (νH.restrict Hslice) :=
      htE.1.mpr ⟨Filter.Eventually.of_forall hκfiber, hnorm⟩
    obtain ⟨hAi, hidentity⟩ := htE.2 hEi
    exact ⟨hEi, hAabsi, hAi, hidentity⟩

end Langlands.AllField.RankinSelberg
