import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationComodule
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Serre's criterion for affine quotients of étale equivalence relations

An étale equivalence relation on a Noetherian affine scheme, with affine relation scheme
embedded as a closed subscheme of `U × U`, all of whose modules are acyclic, has an affine
quotient.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- If `E` is an étale equivalence relation with `E.U` affine and Noetherian, `E.R` affine and
`j = (t, s) : E.R ⟶ E.U ⨯ E.U` a closed immersion, and every module on the groupoid of `E` is
acyclic, then `E` has an affine quotient. -/
def EtaleEquivalenceRelationSerreCriterionStatement : Prop :=
  ∀ E : EtaleEquivalenceRelation.{u}, IsAffine E.U → IsNoetherian E.U → IsAffine E.R →
    IsClosedImmersion (prod.lift E.t E.s) → E.ComodulesAcyclic → E.HasAffineQuotient

end Langlands.AlgebraicGeometry
