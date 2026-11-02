import Langlands.Representation.Category.Abelian
import Langlands.Representation.Category.Subquotients
import Langlands.CategoryTheory.RenardFiniteType
import Langlands.CategoryTheory.Renard.CompositionChains

/-!
# The irreducible-existence assertions of Renard III.1.4

The source categorical finiteness predicates and actual smooth
subrepresentation, quotient and subquotient relations are retained.
The necessary nonzero qualification is explicit.
-/

namespace Langlands.SmoothRep

universe uK uG uV

variable {k : Type uK} {G : Type uG}
variable [Field k] [Group G] [TopologicalSpace G]

/-- A nonzero smooth representation has an irreducible subquotient; source
finite type gives an irreducible quotient, and source finite length gives
an irreducible subrepresentation. -/
def RenardIrreducibleExistenceStatement : Prop :=
  ∀ [IsTopologicalGroup G] (A : SmoothRep.{uK, uG, uV} k G),
    Nontrivial A →
      (∃ B : SmoothRep.{uK, uG, uV} k G, B.IsIrreducible ∧ IsSubquotient B A) ∧
      (Langlands.Renard.IsFiniteTypeObject A →
        ∃ B : SmoothRep.{uK, uG, uV} k G, B.IsIrreducible ∧ IsQuotient B A) ∧
      (Langlands.Renard.IsFiniteLength A →
        ∃ B : SmoothRep.{uK, uG, uV} k G, B.IsIrreducible ∧ IsSubrepresentation B A)

end Langlands.SmoothRep
