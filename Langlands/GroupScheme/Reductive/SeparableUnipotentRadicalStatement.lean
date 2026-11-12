import Langlands.GroupScheme.Reductive.UnipotentRadical

/-! # Unipotent radicals under separable algebraic field extension: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Unipotent radicals under separable algebraic extension** (Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, 2nd edition (2015), Proposition 1.1.9(1), for separable algebraic
extensions). Let `K/k` be a separable algebraic field extension and `G` a smooth connected
affine group scheme over `k`.

1. The base change to `K` of a `k`-unipotent radical of `G` is a `K`-unipotent radical of
   `G_K`: `R_{u,k}(G)_K = R_{u,K}(G_K)`.
2. `G` is pseudo-reductive over `k` if and only if `G_K` is pseudo-reductive over `K`. -/
def SeparableAlgebraicUnipotentRadicalStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsSeparable k K]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    Smooth G.X.hom → IsAffineHom G.X.hom → ConnectedSpace G.X.left →
      (∀ (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G),
        IsUnipotentRadical i →
          IsUnipotentRadical
            ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i)) ∧
      (IsPseudoReductive G ↔
        IsPseudoReductive
          ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G))

end Langlands.GroupScheme
