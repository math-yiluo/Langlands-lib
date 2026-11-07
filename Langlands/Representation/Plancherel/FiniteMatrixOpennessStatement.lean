import Langlands.Representation.Unitary.UnitarizabilityContinuationProof

/-! A finite-dimensional auxiliary statement for character-family openness. -/

namespace Langlands.Plancherel

universe uX uJ un

/-- Entrywise continuous complex square-matrix families have an open locus
with no nonzero proper common invariant subspace. -/
def FiniteMatrixIrreducibilityOpennessStatement : Prop :=
  ∀ (X : Type uX) [TopologicalSpace X] (J : Type uJ)
    (n : Type un) [Fintype n] (A : X → J → Matrix n n ℂ),
    (∀ j i k, Continuous (fun x => A x j i k)) →
    IsOpen {x | UnitarizabilityContinuation.IsIrreducibleFamily (A x)}

end Langlands.Plancherel
