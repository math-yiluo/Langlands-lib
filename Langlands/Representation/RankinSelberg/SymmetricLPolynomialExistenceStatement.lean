import Langlands.Representation.RankinSelberg.PadicPairFactors

/-!
# Existence of symmetric p-adic L-polynomials

A closed statement for actual representations of Whittaker type in either rank
order, using the canonical p-adic data and a supplied self-dual Haar measure.
This packages JPSS Theorem 2.7(ii) with the rank convention in Section 2.12.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker Polynomial

universe uF uV uW

/-- Every pair of Whittaker-type representations has a symmetric p-adic
L-polynomial, common to all compatible quotient measures. This is a proposition
definition, not a proof of the analytic existence theorem. -/
def SymmetricLPolynomialExistenceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r n : ℕ)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType r (standardCharacter ψ r) π) →
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType n (standardCharacter ψ n) σ) →
    ∃ P : ℂ[X], IsPadicSymmetricLPolynomial F ψ ν.val π σ P

end Langlands.RankinSelberg
