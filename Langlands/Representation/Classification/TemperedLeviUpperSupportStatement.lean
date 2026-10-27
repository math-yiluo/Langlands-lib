import Langlands.Representation.Classification.RelativeRegularComparisonStatement

/-!
# Upper discrete-series quotient support of tempered product-Levi representations

The middle-to-coarse support step of the initial proof setup of Silberger 1978,
Proposition 5.1, p.99, derived for actual standard product Levis of GL_n.
This is a proposition definition, not a proof.
-/

namespace Langlands

open GeneralLinear Geometric

universe uF uV

/-- Every irreducible analytically tempered representation of an actual
positive-rank product Levi is a quotient of the untwisted upper normalized
refined induction of an irreducible analytically square-integrable
representation of a flattened refinement. -/
def GLTemperedLeviUpperSupportStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n)
      (π : Rep.{uV} ℂ (B.Levi F.Carrier)),
      Representation.IsIrreducible π.ρ →
      RelativeRegularComparison.IsLeviTempered T B π →
      ∃ (Q : BlockRefinement B)
        (σ : Rep.{max uF uV} ℂ ((B.flatten Q).Levi F.Carrier)),
        Representation.IsIrreducible σ.ρ ∧
        RelativeRegularComparison.IsLeviSquareIntegrable T (B.flatten Q) σ ∧
        ∃ q : (RelativeRegularComparison.middleInduced T B Q σ).ρ.IntertwiningMap π.ρ,
          Function.Surjective q

end Langlands
