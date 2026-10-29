import Langlands.Representation.Filtration.ObjectDefinitions

/-! Finite dimensionality from the graded quotients of an actual filtration. -/

namespace Langlands.ObjectRepFiltration

/-- If every actual graded quotient of a finite filtration of a representation
over a field is finite-dimensional, then the representation is
finite-dimensional. This proposition states the claim only. -/
def FiniteDimensionalFromGradedStatement.{uK, uG, uV} : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G]
    (A : Rep.{uV} k G) (n : ℕ) (s : ObjectRepFiltration A n),
    (∀ i : Fin n, FiniteDimensional k (s.gradedRepresentation i)) →
      FiniteDimensional k A

end Langlands.ObjectRepFiltration
