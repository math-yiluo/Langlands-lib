import Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Noetherian finite-surjective descent of affineness for étale equivalence relations

Stacks Project Lemma 69.17.3 (Tag 07VP) in the language of presentations: the statement of
`EtaleEquivalenceRelationAffineDescentStatement` with a Noetherian affine scheme `E.U`.
-/

universe u

open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- If `E` is an étale equivalence relation on a Noetherian affine scheme `E.U`, and `E` has
a finite surjective cartesian cover by an étale equivalence relation with an affine
quotient, then `E` has an affine quotient. -/
def NoetherianEtaleEquivalenceRelationAffineDescentStatement : Prop :=
  ∀ E : EtaleEquivalenceRelation.{u}, IsAffine E.U → IsNoetherian E.U →
    E.HasFiniteSurjectiveCoverWithAffineQuotient → E.HasAffineQuotient

end Langlands.AlgebraicGeometry
