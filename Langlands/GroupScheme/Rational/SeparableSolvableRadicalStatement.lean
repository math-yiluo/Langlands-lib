import Langlands.GroupScheme.Rational.LeviSubgroup

/-! # Solvable radicals under separable algebraic field extension: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Solvable radicals under separable algebraic extension** (Milne, *Algebraic Groups*
(2017), Proposition 19.1). Let `K/k` be a separable algebraic field extension and `G` a
smooth connected affine group scheme over `k`. The base change to `K` of a solvable
radical `R(G)` of `G` (largest smooth connected solvable normal closed subgroup over `k`)
is a solvable radical of `G_K`: `R(G)_K = R(G_K)`. -/
def SeparableAlgebraicSolvableRadicalStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsSeparable k K]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    Smooth G.X.hom → IsAffineHom G.X.hom → ConnectedSpace G.X.left →
      ∀ (R : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ G),
        IsSolvableRadical r →
          IsSolvableRadical
            ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map r)

end Langlands.GroupScheme
