import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationComodule
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Acyclicity of modules on a finitely covered Noetherian étale equivalence relation

An étale equivalence relation on a Noetherian affine scheme, with affine relation scheme
embedded as a closed subscheme of `U × U`, and with a finite surjective cartesian cover by an
étale equivalence relation with an affine quotient, has only acyclic modules.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- If `E` is an étale equivalence relation with `E.U` affine and Noetherian, `E.R` affine and
`j = (t, s) : E.R ⟶ E.U ⨯ E.U` a closed immersion, and `E` has a finite surjective cartesian cover
by an étale equivalence relation with an affine quotient, then every module on the groupoid of
`E` is acyclic. -/
def EtaleEquivalenceRelationComodulesAcyclicStatement : Prop :=
  ∀ E : EtaleEquivalenceRelation.{u}, IsAffine E.U → IsNoetherian E.U → IsAffine E.R →
    IsClosedImmersion (prod.lift E.t E.s) →
      E.HasFiniteSurjectiveCoverWithAffineQuotient → E.ComodulesAcyclic

end Langlands.AlgebraicGeometry
