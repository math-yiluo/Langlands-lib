import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.Representation.Shahidi.Induction
import Mathlib.Algebra.Module.ULift

/-!
# Equal-rank rank-one extension reverse divisibility

An internal prerequisite for the first general-rank descent step in JPSS
section 7.2. The test and induced ranks are both `t + 2`, beyond the rank
range printed in Lemma (5.5). This module only defines the proposition;
it supplies neither its proof nor the equal-rank analytic comparison.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear Polynomial

universe uF uV uW

/-- The equal-rank reverse L-polynomial divisibility prerequisite for the
actual upper normalized induction in ordered blocks `(χ, σ₁)`. Both
certified polynomials are conclusions. The only representation hypotheses
are Whittaker type of `π` and `σ₁`; their carriers and the field have
independent universes. This is an internal statement target, not the
literal rank-restricted JPSS Lemma (5.5). -/
def EqualRankRankOneExtensionLDivisibilityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (t : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (t + 2) F.Carrier) V)
    (σ₁ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier),
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType (t + 1) (standardCharacter ψ (t + 1)) π) →
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType t (standardCharacter ψ t) σ₁) →
    let χlift : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier)
        (ULift.{uW} ℂ) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp
        (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ))
    ∃ Pbase Pind : ℂ[X],
      IsPadicSymmetricLPolynomial F ψ ν.val π σ₁ Pbase ∧
      IsPadicSymmetricLPolynomial F ψ ν.val π
        (F.canonicalNormalizedProductInduced
          (Shahidi.twoBlocks 1 (t + 1) (Nat.succ_pos 0) (Nat.succ_pos t))
          (Shahidi.pairFamily χlift σ₁)) Pind ∧
      Pbase ∣ Pind

end Langlands.RankinSelberg
