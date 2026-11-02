import Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Noetherian

/-! # A Noetherian first level for separated étale equivalence relations

The first level of absolute Noetherian approximation (Stacks Project Proposition 70.8.1,
Tag 07SU) in the language of presentations: a separated étale equivalence relation on an
affine scheme is the pullback, along a cartesian morphism, of an étale equivalence relation on
a Noetherian affine scheme with an affine relation scheme.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- If `E` is an étale equivalence relation on an affine scheme `E.U` such that
`j = (t, s) : E.R ⟶ E.U ⨯ E.U` is a closed immersion, then there are an étale equivalence
relation `E₀` on a Noetherian affine scheme `E₀.U`, with an affine relation scheme `E₀.R`, and
a cartesian morphism `(f, g) : E ⟶ E₀`. -/
def EtaleEquivalenceRelationNoetherianFirstLevelStatement : Prop :=
  ∀ E : EtaleEquivalenceRelation.{u}, IsAffine E.U →
    IsClosedImmersion (prod.lift E.t E.s) →
      ∃ (E₀ : EtaleEquivalenceRelation.{u}) (f : E.U ⟶ E₀.U) (g : E.R ⟶ E₀.R),
        EtaleEquivalenceRelation.IsCartesianHom E E₀ f g ∧ IsAffine E₀.U ∧
          IsNoetherian E₀.U ∧ IsAffine E₀.R

end Langlands.AlgebraicGeometry
