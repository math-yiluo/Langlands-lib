import Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

/-! # Affine quotients pull back along cartesian morphisms

Descent of affine morphisms along the flat, locally finitely presented quotient map (Stacks
Project Lemma 35.37.1, Tag 0245) in the language of presentations: if an étale equivalence
relation on an affine scheme maps cartesianly to one on an affine scheme with an affine
quotient, then it has an affine quotient itself.
-/

universe u

open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Let `(f, g) : E ⟶ E₀` be a cartesian morphism of étale equivalence relations with `E.U`
and `E₀.U` affine. If `E₀` has an affine quotient, then so does `E`. -/
def EtaleEquivalenceRelationCartesianAffineQuotientStatement : Prop :=
  ∀ (E E₀ : EtaleEquivalenceRelation.{u}) (f : E.U ⟶ E₀.U) (g : E.R ⟶ E₀.R),
    EtaleEquivalenceRelation.IsCartesianHom E E₀ f g → IsAffine E.U → IsAffine E₀.U →
      E₀.HasAffineQuotient → E.HasAffineQuotient

end Langlands.AlgebraicGeometry
