import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonModels
import Langlands.AllField.Representation.RankinSelberg.AnalyticBridge
import Langlands.AllField.Representation.RankinSelberg.GammaFactor
import Langlands.AllField.Representation.Unramified.SphericalConstituentExistenceProof
/-!
# Coefficient-model hypotheses and gamma-equation uniformity

The coefficient image of a full Whittaker-type representation again has full
Whittaker type. A gamma equation at the constructed quotient measure for one
nonzero functional pair transports to every compatible measure and nonzero pair.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairGammaFactor QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement glCoefficientModel_isOfWhittakerType matrixComparisonModelsTopology normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW uG

section Algebraic


end Algebraic

section Models


end Models

section PadicModels

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

/-- The canonical p-adic coefficient model has all three full Whittaker-type
hypotheses required in the matrix-to-rank-one comparison. -/
theorem glCoefficientModel_isOfWhittakerType
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (ℓ : glFunctionals ψ n π) (hℓ : ℓ.val ≠ 0) :
    IsOfWhittakerType n (standardCharacter ψ n)
      (V := (glCoefficientModel ψ n π ℓ).toSubmodule)
      (glModelRepresentation ψ n π ℓ) := by
  exact coefficientModel_isOfWhittakerType
    (Langlands.AllField.Unramified.SphericalExistence.exists_compactOpenSubgroup_le F) hπ ℓ hℓ

end PadicModels

section Uniformity


end Uniformity

end Langlands.AllField.RankinSelberg
