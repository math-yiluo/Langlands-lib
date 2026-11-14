import Langlands.Representation.RankinSelberg.RankOneGammaTwistProof
import Langlands.AllField.Representation.RankinSelberg.RankOneGammaTwistStatement
/-! Transport of the full gamma certificate, including every measure and functional. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement RankOneGammaTwistStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneGammaTwist
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis

universe uF uV

namespace RankOneGammaTwist
open Langlands.RankinSelberg.RankOneGammaTwist
open Langlands.AllField.RankinSelberg.RankOneGammaTwist
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement RankOneGammaTwistStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneGammaTwist
open Langlands.AllField.RankinSelberg

section Relations


end Relations

end RankOneGammaTwist

/-- Rank-one determinant twists transport the unchanged full gamma certificate. -/
theorem rankOneGammaTwist : RankOneGammaTwistStatement.{uF, uV} := by
  intro F _ _ _ _ ψ ν n V hV hVC π χ G
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear 1 F)
  let : BorelSpace (Langlands.GeneralLinear 1 F) := ⟨rfl⟩
  let := borel (upperUnipotent 1 F)
  let : BorelSpace (upperUnipotent 1 F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient 0 F)
  simp only [IsPadicSymmetricGammaFactor, Nat.zero_le, ite_true]
  exact RankOneGammaTwist.pair_factor ψ χ
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) ν π
    (⟨⟩ : LocalFieldData F).residueCardinality G

end Langlands.AllField.RankinSelberg
