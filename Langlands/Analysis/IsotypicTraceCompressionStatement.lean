import Langlands.Analysis.OperatorTrace
import Langlands.Representation.Archimedean.HilbertIntertwinerEvaluation
import Langlands.Representation.Archimedean.SmoothVectors

/-! # Trace compression for an isotypic Hilbert representation

The proposition `IsotypicTraceCompressionStatement` concerns a unitary action `π` on `E` whose
bounded intertwiner ranges from a topologically irreducible unitary action `σ` on `H` span a
dense subspace of `E`. There is a bounded operator `Q` on `E` that commutes with every operator
commuting with `π`. Suppose `X (J x) = J (A x)` for every bounded intertwiner `J` and every
`x : H`. If `A = 0`, then `X = 0`. If `Y` commutes with `π`, `A ≠ 0`, and both `A` and `X Y`
are trace class, then `Q Y` is trace class and `tr(X Y) = tr(A) tr(Q Y)`. -/

noncomputable section

universe uG uH uE

namespace Langlands.Analysis.OperatorIdeals

open Langlands.Archimedean

/-- Let `σ` on `H` and `π` on `E` be unitary actions of a group `G`, with `σ` topologically
irreducible and the ranges of the bounded intertwiners `H → E` spanning a dense subspace of `E`.
There is a bounded `Q` on `E` commuting with every operator that commutes with `π`, such that
whenever `X (J x) = J (A x)` for all bounded intertwiners `J` and all `x`: `A = 0` forces
`X = 0`; and if `Y` commutes with `π`, `A ≠ 0`, and `A` and `X Y` are trace class, then `Q Y`
is trace class and `tr (X Y) = tr A * tr (Q Y)`. -/
def IsotypicTraceCompressionStatement : Prop :=
  ∀ {G : Type uG} [Group G]
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (σ : G →* (H →L[ℂ] H)) (π : G →* (E →L[ℂ] E)),
    (∀ g x y, inner ℂ (σ g x) (σ g y) = inner ℂ x y) →
    (∀ g x y, inner ℂ (π g x) (π g y) = inner ℂ x y) →
    IsTopologicallyIrreducible σ →
    (Submodule.span ℂ {z : E | ∃ (J : boundedIntertwiners σ π) (x : H), z = J.val x}).topologicalClosure = ⊤ →
    ∃ Q : E →L[ℂ] E,
      (∀ Y : E →L[ℂ] E, (∀ g, Commute Y (π g)) → Commute Q Y) ∧
      ∀ (A : H →L[ℂ] H) (X : E →L[ℂ] E),
        (∀ (J : boundedIntertwiners σ π) (x : H), X (J.val x) = J.val (A x)) →
        (A = 0 → X = 0) ∧
        ∀ Y : E →L[ℂ] E, (∀ g, Commute Y (π g)) →
          A ≠ 0 → IsTraceClass A → IsTraceClass (X * Y) →
          IsTraceClass (Q * Y) ∧
            operatorTrace (X * Y) = operatorTrace A * operatorTrace (Q * Y)

end Langlands.Analysis.OperatorIdeals
