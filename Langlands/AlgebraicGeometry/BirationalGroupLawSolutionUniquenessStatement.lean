import Langlands.AlgebraicGeometry.BirationalGroupLaw

/-! # Uniqueness of solutions of birational group laws -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Any two solutions `σ` and `τ` of a birational group law on a smooth, separated, faithfully
flat scheme `X` of finite type over a scheme `S` have isomorphic group schemes: there is
exactly one isomorphism of `S`-group schemes from the group of `σ` to the group of `τ` which
agrees with the two embeddings on the intersection of their domains. -/
def BirationalGroupLawSolutionUniquenessStatement : Prop :=
  ∀ (S X : Scheme.{u}) (f : X ⟶ S),
    Smooth f → IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → Surjective f →
    ∀ (m : BirationalGroupLaw f) (σ τ : m.Solution),
      ∃! e : σ.group ≅ τ.group,
        ∀ (T : Scheme.{u}) (x : T ⟶ σ.domain.toScheme) (y : T ⟶ τ.domain.toScheme),
          x ≫ σ.domain.ι = y ≫ τ.domain.ι →
            x ≫ σ.embedding ≫ e.hom.hom.hom.left = y ≫ τ.embedding

end Langlands.AlgebraicGeometry
