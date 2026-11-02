import Langlands.GroupScheme.Reductive.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Closed linear embeddings of affine algebraic groups over fields -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every affine group scheme of finite type over a field has a finite-dimensional
representation that is a closed immersion of the underlying schemes. -/
def AffineLinearEmbeddingStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsAffineHom G.X.hom → LocallyOfFiniteType G.X.hom →
      ∃ (N : ℕ) (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ

end Langlands.GroupScheme
