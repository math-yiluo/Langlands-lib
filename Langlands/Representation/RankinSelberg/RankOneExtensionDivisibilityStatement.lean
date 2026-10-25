import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.Representation.Shahidi.Induction
import Mathlib.Algebra.Module.ULift

/-!
# Restricted rank-one extension divisibility

JPSS (1983), Lemma (5.5), transported from lower induction `(σ₁, χ)` to
upper induction `(χ, σ₁)`. The test rank is at least two greater than the
rank of `σ₁`. Both certified L-polynomials exist, and the base polynomial
divides the induced polynomial. This module only defines the proposition.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear Polynomial

universe uF uV uW

/-- The upper-parabolic form of JPSS Lemma (5.5), restricted to its original
rank range. The upper blocks are ordered `(χ, σ₁)`. Only the rank-one carrier
is lifted to the universe of `σ₁`, by conjugating the existing rank-one action
through the canonical linear equivalence. No induced Whittaker-type or
factor-existence premise is imposed. -/
def RankOneExtensionLDivisibilityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r t : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ₁ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier),
    t + 3 ≤ r + 1 →
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType r (standardCharacter ψ r) π) →
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
