import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.RelativeIdentityComponent

/-! # Affineness detected by the Weyl quotient of a self-centralizing torus -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The supplied self-centralizing maximal-torus case of SGA 3, Exposé XVI,
Theorem 4.1(d), together with the normalizer and Weyl-quotient existence in
Exposé XV, Proposition 7.1(iv).

A smooth separated quasi-compact group with connected affine residue fibres
and a supplied closed relative maximal torus equal to its full centralizer
has a smooth closed normalizer and a separated quasi-compact étale Weyl
quotient. The quotient map is fppf, its kernel is the given torus on every
test scheme, and the group is affine precisely when this quotient is affine. -/
def SelfCentralizingTorusWeylAffinenessStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S),
    Smooth G.X.hom → IsSeparated G.X.hom → QuasiCompact G.X.hom →
    (∀ s : S,
      ConnectedSpace (RelativeIdentityComponent.residueFiber G s).X.left ∧
        IsAffineHom (RelativeIdentityComponent.residueFiber G s).X.hom) →
    ∀ (T : CommGroupScheme S) (t : T.toGrp ⟶ G),
      RelativeTorus.IsTorus T.toGrp → IsClosedSubgroup t →
      IsFibrewiseMaximalTorus t → (torusCentralizer t).IsRepresentedBy t →
      ∃ (N : GroupScheme S) (n : N ⟶ G)
        (W : GroupScheme S) (q : N ⟶ W),
        IsClosedSubgroup n ∧ (torusNormalizer t).IsRepresentedBy n ∧
        Smooth N.X.hom ∧
        IsSeparated W.X.hom ∧ QuasiCompact W.X.hom ∧ Etale W.X.hom ∧
        Flat q.hom.hom.left ∧ Surjective q.hom.hom.left ∧
        LocallyOfFinitePresentation q.hom.hom.left ∧
        (∀ (U : Over S) (y : U ⟶ N.X),
          y ≫ q.hom.hom = 1 ↔ y ≫ n.hom.hom ∈ (SubgroupFunctor.range t).carrier U) ∧
        (IsAffineHom G.X.hom ↔ IsAffineHom W.X.hom)

end Langlands.GroupScheme
