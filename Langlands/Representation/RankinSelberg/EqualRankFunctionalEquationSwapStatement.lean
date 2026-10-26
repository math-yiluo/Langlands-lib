import Langlands.Representation.RankinSelberg.EqualRankFactorSwapStatement

/-!
# Fixed-character equal-rank epsilon and gamma exchange

This proposition retains exactly the epsilon and gamma conjuncts of
`EqualRankFactorSwapStatement`, with all its quantifiers and hypotheses.
JPSS (2.12) states epsilon symmetry explicitly; gamma symmetry is derived.
This module defines the statement without proving or assuming it.
-/

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker

universe uF uV uW

/-- Exchange of the existing epsilon and gamma certificates for two actual
representations of the same positive rank at the original additive character
and supplied self-dual Haar measure. Both Whittaker-type hypotheses use the
standard character of that same additive character. -/
def EqualRankFunctionalEquationSwapStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (n : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType n (standardCharacter ψ n) π) →
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType n (standardCharacter ψ n) σ) →
    (∀ e : ℂˣ × ℤ,
      IsPadicPairEpsilonFactor F ψ ν.val π σ e ↔
        IsPadicPairEpsilonFactor F ψ ν.val σ π e) ∧
    (∀ G : RationalFunctions,
      IsPadicPairGammaFactor F ψ ν.val π σ G ↔
        IsPadicPairGammaFactor F ψ ν.val σ π G)

end Langlands.RankinSelberg
