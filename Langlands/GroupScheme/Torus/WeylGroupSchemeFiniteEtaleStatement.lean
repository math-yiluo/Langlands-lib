import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.Reductive.Basic

/-! # Statement: the Weyl group scheme of a maximal torus is finite étale -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **The Weyl group scheme of a maximal torus is finite étale** (Conrad, *Reductive group
schemes* (2014), Proposition 3.2.8). Let `G` be a reductive group scheme over a scheme `S`
and `t : T ⟶ G` a closed relative torus that is a maximal torus on every residue-field fibre.
Then the normalizer `N_G(T)` and the centralizer `Z_G(T)` are represented by closed subgroups
`n : N ⟶ G` and `z : Z ⟶ G`, and there is a group scheme `W` over `S`, finite and étale over
`S`, with a homomorphism `q : N ⟶ W` that is flat, surjective and locally of finite
presentation and whose kernel is `Z_G(T)`. So `W` is the fppf quotient
`W_G(T) = N_G(T)/Z_G(T)`. -/
def WeylGroupSchemeFiniteEtaleStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S), IsReductive G →
    ∀ (T : CommGroupScheme S) (t : T.toGrp ⟶ G),
      RelativeTorus.IsTorus T.toGrp → IsClosedSubgroup t → IsFibrewiseMaximalTorus t →
      ∃ (N : GroupScheme S) (n : N ⟶ G) (Z : GroupScheme S) (z : Z ⟶ G)
        (W : GroupScheme S) (q : N ⟶ W),
        IsClosedSubgroup n ∧ (torusNormalizer t).IsRepresentedBy n ∧
        IsClosedSubgroup z ∧ (torusCentralizer t).IsRepresentedBy z ∧
        IsFinite W.X.hom ∧ Etale W.X.hom ∧
        Flat q.hom.hom.left ∧ Surjective q.hom.hom.left ∧
        LocallyOfFinitePresentation q.hom.hom.left ∧
        ∀ (U : Over S) (y : U ⟶ N.X),
          y ≫ q.hom.hom = 1 ↔ y ≫ n.hom.hom ∈ (torusCentralizer t).carrier U

end Langlands.GroupScheme
