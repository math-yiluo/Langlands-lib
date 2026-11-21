import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Statement: extensions of connected groups of multiplicative type -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Theorem 15.39. Let `k` be a field and let `e → N → G → Q → e` be an exact sequence
of affine algebraic groups over `k`: `i : N ⟶ G` is a closed subgroup and `q : G ⟶ Q` is an
fppf quotient map with kernel the image of `i`. If `N` and `Q` are of multiplicative type and
`Q` is connected, then `G` is of multiplicative type. -/
def MultiplicativeTypeConnectedExtensionStatement : Prop :=
  ∀ (k : Type u) [Field k] (N G Q : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] (i : N ⟶ G) (q : G ⟶ Q),
    IsClosedSubgroup i → RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q →
    IsMultiplicativeType N → IsMultiplicativeType Q → ConnectedSpace Q.X.left →
      IsMultiplicativeType G

end Langlands.GroupScheme
