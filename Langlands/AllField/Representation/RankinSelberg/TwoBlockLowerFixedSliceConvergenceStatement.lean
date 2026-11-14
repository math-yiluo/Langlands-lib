import Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceConvergenceStatement
import Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergenceStatement
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerUnfoldingIntegrandData
/-!
# Absolute convergence on every determinant slice of the Section 4.7 lower quotient

JPSS (1983), Section 4.7, printed pages 412–414. This proposition states absolute
convergence of the actual descended lower integrand for sufficiently large opposite
real twists. The bound follows the full Whittaker-type test representation and the
supplied functionals and precedes the real parameter, quotient measure, section,
coefficient, row Schwartz function and determinant-slice integer.

Compatible standard quotient measures exist for the exact normalized group and
unipotent Haar measures. Every compatible measure and its transport by the inverse
of `[g] ↦ [Crot * g]` are sigma-finite. On each slice the proposition asserts
measurability, both absolute-integrability conclusions, and the complex and norm
integral transport identities. This is a statement, not a proof of convergence.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockLowerFixedSliceConvergenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

/-- Fixed-determinant-slice absolute convergence of the unweighted integrand in
JPSS (4.7.1), with the supplied self-dual Fourier measure and the lower quotient
measure transported from every compatible standard quotient measure. Full standard
Whittaker type is assumed for the test representation and both blocks; all supplied
functionals, including zero, and all actual coefficient-image vectors are retained.
The single real bound may depend on the test representation and all preceding data. -/
def TwoBlockLowerFixedSliceConvergenceStatement : Prop :=
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
    letI := T.generalLinearTopologicalGroup (t + 1)
    let G := GeneralLinear (t + 1) F
    let N := upperUnipotent (t + 1) F
    let NQ := LeftUnipotentQuotient t F
    let HQ := TwoBlockLowerUnipotentQuotient.LowerQuotient h F
    letI : MeasurableSpace G := borel G
    letI : BorelSpace G := ⟨rfl⟩
    letI : MeasurableSpace N := borel N
    letI : BorelSpace N := ⟨rfl⟩
    letI : MeasurableSpace NQ := borel NQ
    letI : BorelSpace NQ := ⟨rfl⟩
    letI : MeasurableSpace HQ := borel HQ
    letI : BorelSpace HQ := ⟨rfl⟩
    let μG : Measure G := generalLinearHaar F t
    let μN : Measure N := unipotentHaar F t
    ∃ hN : Measure.IsMulRightInvariant μN,
      letI := hN
      (∃ νN : Measure NQ, IsCompatible N μG μN νN) ∧
      (∀ νN : Measure NQ, IsCompatible N μG μN νN →
        SigmaFinite νN ∧
          SigmaFinite (Measure.map
            (TwoBlockLowerUnipotentQuotient.lowerToStandard h F).symm νN)) ∧
      ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
        (π : Representation ℂ G V),
        IsOfWhittakerType t (standardCharacter ψ t) π →
        ∀ (lambda : glFunctionals ψ t π)
          {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
          (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)),
          (∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i)) →
          ∀ ell : ∀ i, glInverseFunctionals ψ (m i) (τ i),
          ∃ C : ℝ, ∀ u : ℝ, C < u →
            ∀ νN : Measure NQ, IsCompatible N μG μN νN →
              let νMinus : Measure HQ := Measure.map
                (TwoBlockLowerUnipotentQuotient.lowerToStandard h F).symm νN
              ∀ (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h (twoBlockOppositeTwistBlocks F m τ u))
                (Wtest : (coefficientModel π lambda).toSubmodule)
                (Φ : SchwartzBruhat (Fin (t + 1) → F)) (k : ℤ),
                let E : HQ → ℂ := Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.integrand
                  (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i))
                  f Wtest.val Φ ν.val
                let Estandard : NQ → ℂ := fun q =>
                  E ((TwoBlockLowerUnipotentQuotient.lowerToStandard h F).symm q)
                let lowerSlice := Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k
                let standardSlice := Langlands.AllField.RankinSelberg.determinantSlice T t k
                Measurable E ∧
                Integrable E (νMinus.restrict lowerSlice) ∧
                Integrable Estandard (νN.restrict standardSlice) ∧
                (∫ z, E z ∂νMinus.restrict lowerSlice) =
                  (∫ q, Estandard q ∂νN.restrict standardSlice) ∧
                (∫ z, ‖E z‖ ∂νMinus.restrict lowerSlice) =
                  (∫ q, ‖Estandard q‖ ∂νN.restrict standardSlice)

end Langlands.AllField.RankinSelberg
