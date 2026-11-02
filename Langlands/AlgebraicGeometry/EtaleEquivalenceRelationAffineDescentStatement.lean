import Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

/-! # Finite-surjective descent of affineness for étale equivalence relations

Stacks Project Lemma 70.15.1 (Tag 07VS) in the language of presentations: an étale
equivalence relation on an affine scheme with a finite surjective cartesian cover by a
relation with an affine quotient has an affine quotient itself.
-/

universe u

open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- If `E` is an étale equivalence relation on an affine scheme `E.U`, and `E` has a finite
surjective cartesian cover by an étale equivalence relation with an affine quotient, then
`E` has an affine quotient. -/
def EtaleEquivalenceRelationAffineDescentStatement : Prop :=
  ∀ E : EtaleEquivalenceRelation.{u}, IsAffine E.U →
    E.HasFiniteSurjectiveCoverWithAffineQuotient → E.HasAffineQuotient

end Langlands.AlgebraicGeometry
