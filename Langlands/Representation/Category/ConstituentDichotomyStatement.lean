import Langlands.Representation.Category.Subquotients

/-! The simple-subquotient dichotomy across an actual invariant subspace. -/

namespace Langlands.SmoothRep

universe uR uG uV

/-- An irreducible actual subquotient of a smooth representation is an actual
subquotient of a given invariant subrepresentation or of the corresponding
actual quotient. The coefficient field, group and carrier universes are
independent; the topology on the group is arbitrary, and no admissibility,
finite-dimensionality, finite-length or local-compactness hypothesis is made. -/
def IrreducibleSubquotientDichotomy : Prop :=
  ∀ (R : Type uR) [Field R] (G : Type uG) [Group G] [TopologicalSpace G]
    (A D : SmoothRep.{uR, uG, uV} R G) (S : Subrepresentation A.representation),
    D.IsIrreducible → IsSubquotient D A →
      IsSubquotient D (subrepresentation A S) ∨ IsSubquotient D (quotient A S)

end Langlands.SmoothRep
