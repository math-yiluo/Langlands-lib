import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentIdentityStatement
import Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergenceStatement
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerUnfoldingIntegrandData
import Langlands.AllField.Representation.RankinSelberg.TwoBlockUnfoldingIntegrandData
/-!
# The polynomial-cleared first-block JPSS Laurent identity

JPSS (1983), Section 4.7 equation (1), printed page 412, and the first-block
functional-equation calculation in Section 4.9, printed pages 416–418.
This module states the identity in the module of bilateral coefficient functions
under finite Laurent convolution, retaining the actual normalized generators.
Convergence is unconditional in the small-block epsilon certificate. The common
epsilon witnesses precede all sections, coefficient vectors and Schwartz tests.
No analytic proof or cancellation of polynomial factors is supplied here.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt TwoBlockFirstBlockLaurentIdentityStatement TwoBlockJacquetConvergenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

/-- The coefficientwise, polynomial-cleared first-block identity of JPSS (4.7.1).
The total test rank is `t + 1`, the blocks have sizes `m 0 + 1` and `m 1 + 1`,
and the single bound follows every representation and supplied functional.
For every compatible pair of the normalized quotient measures, all coefficients
are absolutely integrable; a supplied first-block epsilon equation then has
common normalized-generator witnesses giving the finite Laurent identity. -/
def TwoBlockFirstBlockLaurentIdentityStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F],
    let T := (⟨⟩ : LocalFieldData F)
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.secondCountableTopology
    letI : MeasurableSpace F := borel F
    letI : BorelSpace F := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F)
      (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar T ψ)
      (t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1),
    let hlt : m 0 < t := by
      have hsum : m 0 + 1 + (m 1 + 1) = t + 1 := by
        simpa only [Fin.sum_univ_two] using h
      omega
    letI := T.generalLinearTopologicalGroup (t + 1)
    letI := T.generalLinearTopologicalGroup (m 0 + 1)
    let G := GeneralLinear (t + 1) F
    let N := upperUnipotent (t + 1) F
    let GA := GeneralLinear (m 0 + 1) F
    let NA := upperUnipotent (m 0 + 1) F
    let NQ := LeftUnipotentQuotient t F
    let AQ := LeftUnipotentQuotient (m 0) F
    let HQ := TwoBlockUnipotentQuotient.BlockQuotient h F
    let LQ := TwoBlockLowerUnipotentQuotient.LowerQuotient h F
    letI : MeasurableSpace G := borel G
    letI : BorelSpace G := ⟨rfl⟩
    letI : MeasurableSpace N := borel N
    letI : BorelSpace N := ⟨rfl⟩
    letI : MeasurableSpace GA := borel GA
    letI : BorelSpace GA := ⟨rfl⟩
    letI : MeasurableSpace NA := borel NA
    letI : BorelSpace NA := ⟨rfl⟩
    letI : MeasurableSpace NQ := borel NQ
    letI : BorelSpace NQ := ⟨rfl⟩
    letI : MeasurableSpace AQ := borel AQ
    letI : BorelSpace AQ := ⟨rfl⟩
    letI : MeasurableSpace HQ := borel HQ
    letI : BorelSpace HQ := ⟨rfl⟩
    letI : MeasurableSpace LQ := borel LQ
    letI : BorelSpace LQ := ⟨rfl⟩
    let μG : Measure G := generalLinearHaar F t
    let μN : Measure N := unipotentHaar F t
    let μGA : Measure GA := generalLinearHaar F (m 0)
    let μNA : Measure NA := unipotentHaar F (m 0)
    let μR := rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)
    let q := T.residueCardinality
    let abv := normalizedAbsoluteValue T
    ∃ (hN : Measure.IsMulRightInvariant μN) (hNA : Measure.IsMulRightInvariant μNA),
      letI := hN
      letI := hNA
      (∃ νN : Measure NQ, IsCompatible N μG μN νN) ∧
      (∃ νA : Measure AQ, IsCompatible NA μGA μNA νA) ∧
      ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
        (π : Representation ℂ G V),
        IsOfWhittakerType t (standardCharacter ψ t) π →
        ∀ (lambda : glFunctionals ψ t π)
          {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
          (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)),
          (∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i)) →
          ∀ ell : ∀ i, glInverseFunctionals ψ (m i) (τ i),
          ∃ C : ℝ, ∀ u : ℝ, C < u →
            let σu := twoBlockOppositeTwistBlocks F m τ u
            let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)
            ∀ (νN : Measure NQ) (νA : Measure AQ),
              IsCompatible N μG μN νN → IsCompatible NA μGA μNA νA →
              let νMinus : Measure LQ := Measure.map
                (TwoBlockLowerUnipotentQuotient.lowerToStandard h F).symm νN
              SigmaFinite νN ∧ SigmaFinite νA ∧ SigmaFinite νMinus ∧
              (∀ (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σu)
                (Wtest : (coefficientModel π lambda).toSubmodule)
                (Φ : SchwartzBruhat (Fin (t + 1) → F)),
                let Eup : HQ → ℂ := Langlands.AllField.RankinSelberg.TwoBlockUnfolding.integrand ellu f Wtest.val Φ
                let Aup : NQ → ℂ := Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.radicalAverage F h μR Eup
                let Elow : LQ → ℂ := Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.integrand ellu f Wtest.val Φ ν.val
                Measurable Aup ∧ Measurable Elow ∧
                ∀ k : ℤ,
                  Integrable Aup (νN.restrict (Langlands.AllField.RankinSelberg.determinantSlice T t k)) ∧
                  Integrable Elow
                    (νMinus.restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k))) ∧
              (∀ (cε : ℂˣ) (d : ℤ),
                UnequalRankEpsilonEquation hlt q ψ abv νA ν.val
                  π (σu 0) lambda (ellu 0) cε d →
                ∃ (ζ : ℂˣ) (P Pdual : Polynomial ℂ),
                  HasModelMinusOneScalar (σu 0) (ellu 0) ζ ∧
                  (∀ (j k : ℕ) (hr : t = m 0 + (j + k + 1)),
                    IsNormalizedGenerator
                      (unequalRankValuesAt j k hr q ψ abv νA
                        (rectangularMeasure ν.val j (m 0 + 1))
                        π (σu 0) lambda (ellu 0)) P ∧
                    IsNormalizedGenerator
                      (dualUnequalRankRationalValuesAt hlt j k hr q ψ abv νA ν.val
                        π (σu 0) lambda (ellu 0)) Pdual ∧
                    ∀ fsmall : (coefficientModel π lambda).toSubmodule,
                    ∀ ffirst : (coefficientModel (σu 0) (ellu 0)).toSubmodule,
                      ∃ R Rdual : RationalFunctions,
                        HasRationalContinuation q
                          (unequalRankIntegralAt j k hr ψ abv νA
                            (rectangularMeasure ν.val j (m 0 + 1)) fsmall.val ffirst.val) R ∧
                        HasRationalContinuation q
                          (dualUnequalRankModelIntegralAt hlt j k hr ψ abv νA ν.val
                            π (σu 0) lambda (ellu 0) fsmall ffirst) Rdual ∧
                        NormalizedFunctionalEquation q P Pdual ζ cε t d R Rdual) ∧
                  ∀ (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σu)
                    (Wtest : (coefficientModel π lambda).toSubmodule)
                    (Φ : SchwartzBruhat (Fin (t + 1) → F)),
                    let Eup : HQ → ℂ := Langlands.AllField.RankinSelberg.TwoBlockUnfolding.integrand ellu f Wtest.val Φ
                    let Aup : NQ → ℂ := Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.radicalAverage F h μR Eup
                    let Elow : LQ → ℂ := Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.integrand ellu f Wtest.val Φ ν.val
                    let Zup : BilateralLaurentSeries := fun k =>
                      ∫ z, Aup z ∂νN.restrict (Langlands.AllField.RankinSelberg.determinantSlice T t k)
                    let Zlow : BilateralLaurentSeries := fun k =>
                      ∫ z, Elow z
                        ∂νMinus.restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k)
                    let D : LaurentPolynomial ℂ := Polynomial.eval₂ LaurentPolynomial.C
                      (LaurentPolynomial.C ((q : ℂ)⁻¹) * LaurentPolynomial.T (-1)) Pdual
                    D • Zlow =
                      (LaurentPolynomial.C ((ζ : ℂ) ^ t * (cε : ℂ)) *
                        LaurentPolynomial.T d * P.toLaurent) • Zup)

end Langlands.AllField.RankinSelberg
