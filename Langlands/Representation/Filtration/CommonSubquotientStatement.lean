import Langlands.Representation.Filtration.ObjectDefinitions
import Langlands.Representation.Category.Subquotients

/-! A common actual irreducible subquotient of representations in independent universes. -/

namespace Langlands

universe uK uG uV uW

variable {k : Type uK} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]

/-- Two actual subquotients, one irreducible, and an equivariant linear equivalence.
The carriers of the ambient representations need not inhabit the same universe. -/
def HaveCommonIrreducibleSubquotient
    (A : SmoothRep.{uK, uG, uV} k G) (B : SmoothRep.{uK, uG, uW} k G) : Prop :=
  ∃ (S : Subrepresentation A.representation)
    (Q : Subrepresentation (SmoothRep.subrepresentation A S).representation)
    (S' : Subrepresentation B.representation)
    (Q' : Subrepresentation (SmoothRep.subrepresentation B S').representation),
    (SmoothRep.subquotient A S Q).IsIrreducible ∧
    Nonempty ((SmoothRep.subquotient A S Q).representation.Equiv
      (SmoothRep.subquotient B S' Q').representation)

/-- Matching actual composition factors of nonzero smooth representations supply
a common actual irreducible subquotient. Nonzeroness is required only of the source. -/
def SameFactorsCommonSubquotientStatement : Prop :=
  ∀ (A : SmoothRep.{uK, uG, uV} k G) (B : SmoothRep.{uK, uG, uW} k G),
    Nontrivial A → HaveSameJordanHolderFactors A.obj B.obj →
    HaveCommonIrreducibleSubquotient A B

end Langlands
