import Langlands.Geometry.Analytic.Affinoid
import Mathlib.Topology.Algebra.Ring.Ideal

/-! # Exact target for bounded maps out of closed-ideal quotients -/

universe u v w

namespace Langlands.Analytic

/-- Bounded maps annihilate ideal closures, descend uniquely to closed-ideal
quotients, and retain every positive linear norm bound under descent. -/
def BoundedQuotientStatement : Prop :=
  ∀ (K : Type u) (A : Type v) (B : Type w)
    [NormedField K] [NormedCommRing A] [NormedCommRing B]
    [NormedAlgebra K A] [NormedAlgebra K B],
    (∀ (φ : BoundedAlgHom K A B) (I : Ideal A),
      (∀ a ∈ I, φ a = 0) → ∀ a ∈ I.closure, φ a = 0) ∧
    (∀ (I : Ideal A) [IsClosed (I : Set A)],
      (∀ (φ : BoundedAlgHom K A B), (∀ a ∈ I, φ a = 0) →
        ∃! ψ : BoundedAlgHom K (A ⧸ I) B,
          ∀ a, ψ (Ideal.Quotient.mk I a) = φ a) ∧
      (∀ (φ : BoundedAlgHom K A B) (ψ : BoundedAlgHom K (A ⧸ I) B),
        (∀ a, ψ (Ideal.Quotient.mk I a) = φ a) →
        ∀ C : ℝ, 0 < C → (∀ a, ‖φ a‖ ≤ C * ‖a‖) →
          ∀ x, ‖ψ x‖ ≤ C * ‖x‖))

end Langlands.Analytic
