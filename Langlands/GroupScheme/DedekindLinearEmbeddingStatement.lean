import Langlands.GroupScheme.Reductive.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.DedekindDomain.Basic

/-! # Closed linear embeddings of flat affine groups over Dedekind domains -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Conrad, Exercise 5.5.7(ii): every flat affine group scheme of finite type over a
Dedekind domain `R` is a closed subgroup of some `GL_N` over `R`. -/
def DedekindLinearEmbeddingStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDedekindDomain R]
    (G : GroupScheme (Spec (CommRingCat.of R))),
    Flat G.X.hom → IsAffineHom G.X.hom → LocallyOfFiniteType G.X.hom →
      ∃ (N : ℕ) (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ

end Langlands.GroupScheme
