import Langlands.Representation.Filtration.ObjectDefinitions
import Mathlib.RingTheory.FiniteLength

/-! A bounded-chain criterion for actual representation composition length. -/

namespace Langlands

/-- An actual representation has a composition series of length at most `b`
exactly when every finite strict chain of invariant subspaces has at most `b`
strict inclusions. Such a series also gives finite length over the monoid
algebra. This declaration states the internal algebraic bridge; it does not
prove either clause. -/
def ObjectCompositionLengthCriterion.{uK, uG, uV} : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G]
    (A : Rep.{uV} k G) (b : ℕ),
    (HasCompositionLengthAtMost A b ↔
      ∀ (m : ℕ) (c : Fin (m + 1) → Subrepresentation A.ρ),
        StrictMono c → m ≤ b) ∧
    (HasCompositionLengthAtMost A b →
      IsFiniteLength (MonoidAlgebra k G) A.ρ.asModule)

end Langlands
