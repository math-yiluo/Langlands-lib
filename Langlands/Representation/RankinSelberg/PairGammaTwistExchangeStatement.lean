import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.Representation.Twist.Definitions

/-!
# Moving a determinant twist between the two factors of a pair gamma factor

For representations `π` of `GL_(r+1)(F)` and `σ` of `GL_(t+1)(F)` and a character `χ` of
`Fˣ`, the pairs `(π ⊗ χ ∘ det, σ)` and `(π, σ ⊗ χ ∘ det)` have the same gamma certificates.
This is an internal consequence of the Rankin–Selberg integral and dual-transform definitions
of Jacquet, Piatetski-Shapiro and Shalika (1983), not a numbered theorem of that paper. It
generalizes `RankOneGammaTwistStatement` (rank-one second factor) to arbitrary ranks. This
module only defines the proposition.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis GeneralLinear

universe uF uV uW

/-- For every representation `π` of `GL_(r+1)(F)`, every representation `σ` of
`GL_(t+1)(F)` (of arbitrary ranks) and every character `χ` of `Fˣ`, a rational function `G`
certifies `γ(s, (π ⊗ χ ∘ det) × σ, ψ)` exactly when it certifies
`γ(s, π × (σ ⊗ χ ∘ det), ψ)`, with the same additive character `ψ` and additive Haar
measure `ν`. Both sides are the existing symmetric p-adic gamma relation, which puts the pair
in larger-rank-first order (the given order when the ranks are equal). -/
def PairGammaTwistExchangeStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    (r t : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (χ : F.Carrierˣ →* ℂˣ) (G : RationalFunctions),
    IsPadicSymmetricGammaFactor F ψ ν (Langlands.twist (χ.comp GeneralLinear.determinant) π)
        σ G ↔
      IsPadicSymmetricGammaFactor F ψ ν π
        (Langlands.twist (χ.comp GeneralLinear.determinant) σ) G

end Langlands.RankinSelberg
