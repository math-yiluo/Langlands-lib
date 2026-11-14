import Langlands.Representation.RankinSelberg.RankOneGammaTwistStatement
import Langlands.AllField.Representation.RankinSelberg.PadicPairFactors
/-!
# Rank-one determinant twists of gamma certificates

Twisting a representation `π` of `GL_(n+1)` by `χ ∘ det` and pairing it with
the trivial character of `GL_1` gives the same gamma certificate as pairing
the untwisted `π` with the rank-one character `χ ∘ det`. This is an internal
consequence of the JPSS (1983) integral and dual-transform definitions, not a
numbered theorem of that paper. This module only defines the proposition.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement RankOneGammaTwistStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.GeneralLinear

universe uF uV

/-- For every representation `π` of `GL_(n+1)(F)` and every character `χ` of
`Fˣ`, a rational function `G` certifies `γ(s, (π ⊗ χ ∘ det) × 1, ψ)` exactly
when it certifies `γ(s, π × χ, ψ)`, with the same additive character `ψ` and
additive Haar measure `ν`. Both sides are the existing full p-adic gamma
relation: the rank-one test is the smaller rank, so each side is the pair
relation with `π` (twisted or not) first. -/
def RankOneGammaTwistStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : letI := borel F
      AdditiveHaarMeasure F)
    (n : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (χ : Fˣ →* ℂˣ) (G : RationalFunctions),
    IsPadicSymmetricGammaFactor F ψ ν (Langlands.twist (χ.comp GeneralLinear.determinant) π)
        (rankOneCharacter (1 : Fˣ →* ℂˣ)) G ↔
      IsPadicSymmetricGammaFactor F ψ ν π (rankOneCharacter χ) G

end Langlands.AllField.RankinSelberg
