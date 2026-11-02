import Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
import Mathlib.AlgebraicGeometry.Noetherian

/-! # A Noetherian level carrying the finite surjective cover

The middle step of the proof of Stacks Project Lemma 70.15.1 (Tag 07VS) in the language of
presentations: over a Noetherian first level, a finite surjective cartesian cover with an
affine quotient descends to a Noetherian level.
-/

universe u

open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Let `(f, g) : E ⟶ E₀` be a cartesian morphism of étale equivalence relations, where
`E.U` is affine, `E₀.U` is a Noetherian affine scheme and `E₀.R` is affine. If `E` has a
finite surjective cartesian cover by an étale equivalence relation with an affine quotient,
then there are an étale equivalence relation `E₁` on a Noetherian affine scheme `E₁.U` with
the same property and a cartesian morphism `(f₁, g₁) : E ⟶ E₁`. -/
def EtaleEquivalenceRelationNoetherianCoverLevelStatement : Prop :=
  ∀ (E E₀ : EtaleEquivalenceRelation.{u}) (f : E.U ⟶ E₀.U) (g : E.R ⟶ E₀.R),
    EtaleEquivalenceRelation.IsCartesianHom E E₀ f g → IsAffine E.U → IsAffine E₀.U →
      IsNoetherian E₀.U → IsAffine E₀.R → E.HasFiniteSurjectiveCoverWithAffineQuotient →
        ∃ (E₁ : EtaleEquivalenceRelation.{u}) (f₁ : E.U ⟶ E₁.U) (g₁ : E.R ⟶ E₁.R),
          EtaleEquivalenceRelation.IsCartesianHom E E₁ f₁ g₁ ∧ IsAffine E₁.U ∧
            IsNoetherian E₁.U ∧ E₁.HasFiniteSurjectiveCoverWithAffineQuotient

end Langlands.AlgebraicGeometry
