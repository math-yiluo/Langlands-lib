import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.Rational.SolvableRadicalQuotient
import Mathlib.FieldTheory.Perfect

/-! # Trivial radical and quotient by the radical over a perfect field: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Semisimplicity from the radical over a perfect field** (Milne, *Algebraic Groups*
(2017), Proposition 19.2). Let `G` be a smooth connected affine group scheme over a
perfect field `k`.

1. If every smooth connected solvable normal closed subgroup of `G` over `k` is trivial
   (`R(G) = e`), then `G` is semisimple.
2. If `r : R ⟶ G` is a solvable radical of `G` over `k` and `q : G ⟶ Q` is an fppf
   quotient of `G` by the image of `r` with `Q` affine, then `Q` (that is, `G/R(G)`) is
   semisimple.

Semisimple is the Library's `IsSemisimple`: connected reductive with finite
scheme-theoretic centre. -/
def PerfectFieldSemisimpleRadicalStatement : Prop :=
  ∀ (k : Type u) [Field k] [PerfectField k] (G : GroupScheme (Spec (CommRingCat.of k))),
    Smooth G.X.hom → IsAffineHom G.X.hom → ConnectedSpace G.X.left →
      (HasTrivialSolvableRadical G → IsSemisimple G) ∧
      ∀ (R : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ G),
        IsSolvableRadical r →
          ∀ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q),
            IsAffineHom Q.X.hom →
              RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) q →
                IsSemisimple Q

end Langlands.GroupScheme
