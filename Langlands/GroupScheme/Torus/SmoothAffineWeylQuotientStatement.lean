import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.Torus.Relative

/-! # Statement: the Weyl quotient of a torus in a smooth affine group -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **The general smooth-affine torus Weyl quotient** (Conrad, *Reductive group schemes*
(2014), Theorem 2.3.1, Proposition 2.1.2 and Lemma 2.2.4), restricted to relative tori.
For a closed relative torus `t : T.toGrp ⟶ G` in a smooth affine group scheme over any
scheme `S`, the actual normalizer and centralizer functors have closed subgroup
representatives `n : N ⟶ G` and `z : Z ⟶ G`. Their fppf quotient is a separated,
quasi-compact, étale group scheme `W`, with a flat, surjective, locally finitely presented
homomorphism `q : N ⟶ W` whose kernel on every test scheme is the centralizer. -/
def SmoothAffineTorusWeylQuotientStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S), Smooth G.X.hom → IsAffineHom G.X.hom →
    ∀ (T : CommGroupScheme S) (t : T.toGrp ⟶ G),
      RelativeTorus.IsTorus T.toGrp → IsClosedSubgroup t →
      ∃ (N : GroupScheme S) (n : N ⟶ G) (Z : GroupScheme S) (z : Z ⟶ G)
        (W : GroupScheme S) (q : N ⟶ W),
        IsClosedSubgroup n ∧ (torusNormalizer t).IsRepresentedBy n ∧
        IsClosedSubgroup z ∧ (torusCentralizer t).IsRepresentedBy z ∧
        IsSeparated W.X.hom ∧ QuasiCompact W.X.hom ∧ Etale W.X.hom ∧
        Flat q.hom.hom.left ∧ Surjective q.hom.hom.left ∧
        LocallyOfFinitePresentation q.hom.hom.left ∧
        ∀ (U : Over S) (y : U ⟶ N.X),
          y ≫ q.hom.hom = 1 ↔ y ≫ n.hom.hom ∈ (torusCentralizer t).carrier U

end Langlands.GroupScheme
