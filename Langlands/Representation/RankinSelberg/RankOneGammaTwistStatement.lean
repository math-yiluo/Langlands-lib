import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.Representation.Twist.Definitions

/-!
# Rank-one determinant twists of gamma certificates

Twisting a representation `π` of `GL_(n+1)` by `χ ∘ det` and pairing it with
the trivial character of `GL_1` gives the same gamma certificate as pairing
the untwisted `π` with the rank-one character `χ ∘ det`. This is an internal
consequence of the JPSS (1983) integral and dual-transform definitions, not a
numbered theorem of that paper. This module only defines the proposition.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis GeneralLinear

universe uF uV

/-- For every representation `π` of `GL_(n+1)(F)` and every character `χ` of
`Fˣ`, a rational function `G` certifies `γ(s, (π ⊗ χ ∘ det) × 1, ψ)` exactly
when it certifies `γ(s, π × χ, ψ)`, with the same additive character `ψ` and
additive Haar measure `ν`. Both sides are the existing full p-adic gamma
relation: the rank-one test is the smaller rank, so each side is the pair
relation with `π` (twisted or not) first. -/
def RankOneGammaTwistStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    (n : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (χ : F.Carrierˣ →* ℂˣ) (G : RationalFunctions),
    IsPadicSymmetricGammaFactor F ψ ν (Langlands.twist (χ.comp GeneralLinear.determinant) π)
        (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) G ↔
      IsPadicSymmetricGammaFactor F ψ ν π (rankOneCharacter χ) G

end Langlands.RankinSelberg
