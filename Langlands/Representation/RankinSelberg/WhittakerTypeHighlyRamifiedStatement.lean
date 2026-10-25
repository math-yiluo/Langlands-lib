import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.Twist.Definitions
import Langlands.HarmonicAnalysis.Conductor

/-!
# Highly ramified L-vanishing for pairs of Whittaker type

JPSS 1983, Proposition 2.13 (printed page 404), in the Whittaker-type scope
of Section 2.1. This proposition definition includes reducible representations
and both rank orders. The conclusion certifies the polynomial `1` in the
existing symmetric pair relation, including its compatible-measure existence
and universal measure quantifiers. No proof of the proposition is supplied.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW

/-- JPSS 1983, Proposition 2.13: for any two representations of Whittaker type
of positive ranks, sufficiently ramified determinant twists of the first have
L-factor `1` against the second. The bound is uniform over all continuous
quasicharacters whose multiplicative conductor is at least that bound.
The supplied self-dual measure and additive character are arbitrary. -/
def WhittakerTypeHighlyRamifiedLVanishingStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ),
    ∀ (r t : ℕ),
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
      {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W),
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType r (standardCharacter ψ r) π) →
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType t (standardCharacter ψ t) σ) →
    ∃ A : ℕ, ∀ χ : (letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier),
      A ≤ F.canonicalTopologicalData.multiplicativeConductor χ →
        IsPadicSymmetricLPolynomial F ψ ν.val
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) σ 1

end Langlands.RankinSelberg
