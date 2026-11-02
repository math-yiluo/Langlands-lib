import Langlands.Representation.Category.Abelian
import Langlands.CategoryTheory.RenardFiniteType
import Langlands.CategoryTheory.Renard.CompositionChains

/-!
# Source finiteness and group-algebra finiteness for smooth representations

Derived comparison targets for the categorical terminology transferred in
Renard III.1.4. The existing category and both finiteness conventions are
retained.
-/

open scoped MonoidAlgebra

namespace Langlands.SmoothRep

universe uR uG uV

variable {R : Type uR} {G : Type uG}
variable [CommRing R] [Group G] [TopologicalSpace G]

/-- Source categorical finite type is finite generation over the actual
group algebra, without a finite-dimensionality assumption. -/
def RenardFiniteTypeStatement : Prop :=
  ∀ [IsTopologicalGroup G] (A : SmoothRep.{uR, uG, uV} R G),
    Langlands.Renard.IsFiniteTypeObject A ↔
      Module.Finite R[G] A.representation.asModule

/-- Source categorical composition length agrees with the existing
group-algebra finite-length predicate. -/
def RenardFiniteLengthStatement : Prop :=
  ∀ [IsTopologicalGroup G] (A : SmoothRep.{uR, uG, uV} R G),
    Langlands.Renard.IsFiniteLength A ↔ A.HasFiniteLength

/-- Both source-to-group-algebra finiteness comparisons. -/
def RenardFinitenessStatement : Prop :=
  RenardFiniteTypeStatement.{uR, uG, uV} (R := R) (G := G) ∧
    RenardFiniteLengthStatement.{uR, uG, uV} (R := R) (G := G)

end Langlands.SmoothRep
