import Langlands.HarmonicAnalysis.AdjacentRankUnipotentFourierStatement
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankIntegralModel
import Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatementSupplement
/-! Source-derived scalar Fourier identity from JPSS Section 6.2, formula (2).
This is a proposition definition, not a proof. -/

noncomputable section

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding AdjacentRankUnipotentFourierStatement PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement padicMatrixFourierSlice padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg
open Langlands.Whittaker

universe uF

/-- The actual rectangular unipotent Fourier identity, retaining both
absolute convergence assertions. The group Haar is the shared normalized
unipotent Haar, while all additive Fourier measures use the supplied self-dual
scalar Haar. No model or representation coefficient occurs in this statement. -/
def AdjacentRankUnipotentFourierStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F],
    letI : MeasurableSpace F := borel F
    haveI : BorelSpace F := ⟨rfl⟩
    haveI : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
    haveI : TotallyDisconnectedSpace F := by
      let : NonarchimedeanRing F := by
        convert! ValuativeRel.nonarchimedeanRing F
        exact Valuation.toTopologicalSpace_eq _
      infer_instance
    ∀ (ψ : UnitaryAdditiveCharacter F)
      (ν : AdditiveHaarMeasure F) (hself : IsSelfDual ψ ν) (r : ℕ),
      letI : MeasurableSpace (upperUnipotent (r + 1) F) := borel _
      haveI : BorelSpace (upperUnipotent (r + 1) F) := ⟨rfl⟩
      ∀ (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F)),
        let w := weylLong (r + 1) F
        let ε := adjacentRankEpsilon F r
        let T := partialFourierEquiv ψ ν (r + 1) hself
        let L : upperUnipotent (r + 1) F → ℂ := fun n =>
          T (rectangularTranslate
            (weylLong (r + 2) F * adjacentRankZeta F r) Φ)
            (rectangularJoin n.val.val ε) *
              (inverseStandardCharacter ψ r n : ℂ)
        let R : upperUnipotent (r + 1) F → ℂ := fun n =>
          rectangularFourierEquiv ψ ν (r + 1) (r + 2) hself (T Φ)
            (rectangularJoin (w.val * n.val.val) (Matrix.mulVec w.val ε)) *
              (standardCharacter ψ r n : ℂ)
        Integrable L (unipotentHaar F r) ∧
          Integrable R (unipotentHaar F r) ∧
          (∫ n, L n ∂unipotentHaar F r) =
            ∫ n, R n ∂unipotentHaar F r

end Langlands.AllField.HarmonicAnalysis
