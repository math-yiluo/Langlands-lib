import Langlands.Representation.RankinSelberg.RankOneAmbientMatrixFunctionalEquationComparisonStatement
import Langlands.AllField.LocalFactor.ResidueReflection
import Langlands.AllField.Representation.GodementJacquet.AnalyticData
import Langlands.AllField.Representation.RankinSelberg.PadicPairFactors
/-!
# Rank-one comparison from an ambient matrix functional equation

This internal conditional statement allows the actual coefficient model to have
its bi-smooth coefficients contained in those of a separate representation.
Normalized generators remain assertions about that ambient representation.
No comparison proof or analytic data existence is supplied here.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement RankOneAmbientMatrixFunctionalEquationComparisonStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Whittaker

universe uF uV uW

/-- Ambient form of the matrix-to-rank-one comparison. Full normalized matrix
data are assumed on `ρ`, and only actual coefficient inclusion is required for
the model of `σ`. The conclusion is the complete symmetric gamma certificate
for the original `σ` and the trivial rank-one test, including `n = 0`.
There is no claim that `P` or `PDual` generates constituent matrix values. -/
def RankOneAmbientMatrixFunctionalEquationComparisonStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F],
    letI : MeasurableSpace F := borel F
    haveI : BorelSpace F := ⟨rfl⟩
    haveI : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
    haveI : TotallyDisconnectedSpace F := by
      let : NonarchimedeanRing F := by
        convert! ValuativeRel.nonarchimedeanRing F
        exact Valuation.toTopologicalSpace_eq _
      infer_instance
    ∀ (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F),
      IsSelfDual ψ ν →
    ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V),
      IsOfWhittakerType n (standardCharacter ψ n) σ →
    ∀ ℓ : glFunctionals ψ n σ, ℓ.val ≠ 0 →
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
      GodementJacquet.biSmoothMatrixCoefficients
          (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
          (glModelRepresentation ψ n σ ℓ) ≤
        GodementJacquet.biSmoothMatrixCoefficients ρ →
    ∀ (P PDual : Polynomial ℂ) (c : ℂˣ) (a : ℤ),
      Langlands.AllField.GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ ν
          ρ P PDual c a →
        IsPadicSymmetricGammaFactor F ψ ν σ
          (rankOneCharacter (1 : Fˣ →* ℂˣ))
          (rationalGammaExpression (Langlands.AllField.LocalFactor.residueReflection F) c a P PDual)

end Langlands.AllField.RankinSelberg
