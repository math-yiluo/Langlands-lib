import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.MultiplicativeType

/-! # Unipotent groups and groups of multiplicative type (Milne 14.16–14.18) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Proposition 14.16 and Corollaries 14.17 and 14.18, for affine algebraic groups
over a field `k`:
1. a group that is both of multiplicative type and unipotent is trivial;
2. a unipotent closed subgroup and a closed subgroup of multiplicative type of the same group
   intersect trivially;
3. every homomorphism from a unipotent group to a group of multiplicative type, and every
   homomorphism from a group of multiplicative type to a unipotent group, is trivial. -/
def UnipotentMultiplicativeTrivialityStatement : Prop :=
  ∀ (k : Type u) [Field k],
    (∀ (G : GroupScheme (Spec (CommRingCat.of k)))
        [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom],
      IsMultiplicativeType G → IsUnipotent G → SubgroupFunctor.range (𝟙 G) = ⊥) ∧
    (∀ (G U M : GroupScheme (Spec (CommRingCat.of k)))
        [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] (i : U ⟶ G) (j : M ⟶ G),
      IsClosedSubgroup i → IsClosedSubgroup j → IsUnipotent U → IsMultiplicativeType M →
        SubgroupFunctor.range i ⊓ SubgroupFunctor.range j = ⊥) ∧
    (∀ (U M : GroupScheme (Spec (CommRingCat.of k)))
        [LocallyOfFiniteType U.X.hom] [IsAffineHom U.X.hom]
        [LocallyOfFiniteType M.X.hom] [IsAffineHom M.X.hom],
      IsUnipotent U → IsMultiplicativeType M →
        (∀ f : U ⟶ M, SubgroupFunctor.range f = ⊥) ∧
          (∀ f : M ⟶ U, SubgroupFunctor.range f = ⊥))

end Langlands.GroupScheme
