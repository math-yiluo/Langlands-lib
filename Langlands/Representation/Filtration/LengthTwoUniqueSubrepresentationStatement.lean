import Langlands.Representation.Filtration.ObjectDefinitions
import Langlands.Representation.Category.Subquotients

/-! A derived algebraic criterion for a unique nonzero proper invariant subspace. -/

namespace Langlands

universe uK uG uV uW

/-- A reducible smooth representation with a strict natural count bounded by two,
and a nonzero intertwiner killing every count-one invariant subspace, has an
actual length-two composition series and a unique nonzero proper invariant
subspace. That subspace and its actual quotient are irreducible. -/
def LengthTwoUniqueSubrepresentationCriterion : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Group G] [TopologicalSpace G]
    (A : SmoothRep.{uK, uG, uV} k G)
    (W : Type uW) [AddCommGroup W] [Module k W]
    (σ : Representation k G W) (μ : Subrepresentation A.representation → ℕ),
    StrictMono μ → μ ⊥ = 0 → μ ⊤ ≤ 2 →
    ∀ f : A.representation.IntertwiningMap σ, f ≠ 0 →
    ¬ A.IsIrreducible →
    (∀ S : Subrepresentation A.representation, μ S = 1 → S ≤ f.ker) →
    HasCompositionSeriesLength A.obj 2 ∧
      (∃! S : Subrepresentation A.representation, S ≠ ⊥ ∧ S ≠ ⊤) ∧
      ∀ S : Subrepresentation A.representation, S ≠ ⊥ → S ≠ ⊤ →
        (SmoothRep.subrepresentation A S).IsIrreducible ∧
          (SmoothRep.quotient A S).IsIrreducible

end Langlands
