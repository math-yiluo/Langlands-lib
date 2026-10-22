import Langlands.Representation.Filtration.ObjectDefinitions
import Langlands.Representation.Category.Subquotients

/-! An actual irreducible smooth subquotient is equivalent to a graded quotient
of any supplied composition series. -/

namespace Langlands

/-- For a supplied composition series `s` of a smooth representation `A`, every
irreducible `D` equivalent to an actual smooth subquotient `S/U` of `A` is
equivalent to some actual graded quotient of `s`. The carriers of `A` and `D`
lie in independent universes, and the length `r` may be zero. -/
def SimpleSubquotientFactorTheorem.{uK, uG, uV, uW} : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Group G] [TopologicalSpace G]
    (A : SmoothRep.{uK, uG, uV} k G) (r : ℕ)
    (s : ObjectRepFiltration (Rep.of A.representation) r),
    s.HasSimpleFactors →
    ∀ (D : SmoothRep.{uK, uG, uW} k G)
      (S : Subrepresentation A.representation)
      (U : Subrepresentation (SmoothRep.subrepresentation A S).representation),
      D.IsIrreducible →
      Nonempty (D.representation.Equiv (SmoothRep.subquotient A S U).representation) →
      ∃ j : Fin r, Nonempty (D.representation.Equiv (s.gradedRepresentation j).ρ)

end Langlands
