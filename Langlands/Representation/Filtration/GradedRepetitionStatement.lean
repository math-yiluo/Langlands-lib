import Langlands.Representation.Filtration.ObjectDefinitions

/-! Repeated nonzero graded pieces force repeated composition factors. -/

namespace Langlands

universe uK uG uY

/-- If two distinct graded pieces of a finite filtration are equivalent and
nonzero, every actual composition series of the ambient representation
contains two distinct equivalent factors. -/
def GradedFactorRepetitionCriterion : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G]
    (Y : Rep.{uY} k G) (N m : ℕ) (t : ObjectRepFiltration Y N),
    t.HasSimpleFactors →
    ∀ (u : ObjectRepFiltration Y m) (i j : Fin m),
      i ≠ j →
      (u.gradedRepresentation i).ρ.Equiv (u.gradedRepresentation j).ρ →
      Nontrivial (u.gradedRepresentation i) →
      ∃ a b : Fin N, a ≠ b ∧
        Nonempty ((t.gradedRepresentation a).ρ.Equiv (t.gradedRepresentation b).ρ)

end Langlands
