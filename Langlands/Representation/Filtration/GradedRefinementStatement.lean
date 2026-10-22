import Langlands.Representation.Filtration.ObjectDefinitions

/-! Actual Jordan–Hölder factor matching from matching graded pieces of
supplied finite filtrations. -/

namespace Langlands

universe uK uG uA uB

/-- Two supplied finite filtrations of the same length, whose graded pieces
have matching actual Jordan–Hölder factors after a permutation of the indices,
give matching actual Jordan–Hölder factors of the two ambient representations.
The filtrations need not have simple or nonzero graded pieces. This proposition
states the claim only. -/
def GradedJordanHolderRefinementStatement : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G]
    (A : Rep.{uA} k G) (B : Rep.{uB} k G) (n : ℕ)
    (f : ObjectRepFiltration A n) (g : ObjectRepFiltration B n)
    (e : Equiv.Perm (Fin n)),
    (∀ i : Fin n,
      HaveSameJordanHolderFactors (f.gradedRepresentation i)
        (g.gradedRepresentation (e i))) →
      HaveSameJordanHolderFactors A B

end Langlands
