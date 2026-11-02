import Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The relation scheme of a finitely covered étale equivalence relation

An étale equivalence relation on an affine scheme with a finite surjective cartesian cover
admitting an affine quotient has an affine relation scheme, embedded as a closed subscheme of
`U × U`.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- If `E` is an étale equivalence relation on an affine scheme `E.U`, and `E` has a finite
surjective cartesian cover by an étale equivalence relation with an affine quotient, then the
scheme `E.R` is affine and `j = (t, s) : E.R ⟶ E.U ⨯ E.U` is a closed immersion. -/
def EtaleEquivalenceRelationAffineRelationStatement : Prop :=
  ∀ E : EtaleEquivalenceRelation.{u}, IsAffine E.U →
    E.HasFiniteSurjectiveCoverWithAffineQuotient →
      IsAffine E.R ∧ IsClosedImmersion (prod.lift E.t E.s)

end Langlands.AlgebraicGeometry
