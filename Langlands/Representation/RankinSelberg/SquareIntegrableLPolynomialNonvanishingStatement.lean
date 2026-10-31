import Langlands.Representation.RankinSelberg.TemperedLFactorStatement

/-!
# Nonvanishing of an existing square-integrable pair L-polynomial

This internal proposition keeps the quantifiers and hypotheses of
`SquareIntegrablePoleFreeStatement` and replaces its existential conclusion by
the conditional one: every L-polynomial of the pair, if it exists, has no zero
in the open unit disk. It is a statement, not a proof, and it does not assert
that the L-polynomial exists.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Polynomial

universe uF uV uW

/-- For irreducible square-integrable `π` and `σ` of any ranks, every polynomial
`P` satisfying the symmetric pair L-polynomial relation has no zero `z` with
`‖z‖ < 1`. This is the conditional, pole-freeness part of
`SquareIntegrablePoleFreeStatement`; existence of `P` is not asserted. -/
def SquareIntegrableLPolynomialNonvanishingStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r t : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W),
    Representation.IsIrreducible π → F.canonicalTopologicalData.IsSquareIntegrable π →
    Representation.IsIrreducible σ → F.canonicalTopologicalData.IsSquareIntegrable σ →
    ∀ P : ℂ[X], IsPadicSymmetricLPolynomial F ψ ν.val π σ P →
      ∀ z : ℂ, ‖z‖ < 1 → P.eval z ≠ 0

end Langlands.RankinSelberg
