import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.GroupScheme.Rational.TorusNormalizer

/-! # Statement: the centralizer of a multiplicative subgroup is open in its normalizer -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **The centralizer of a subgroup of multiplicative type is open in its normalizer**
(Milne, *Algebraic Groups* (2017), Corollary 12.40). Let `k` be a field, `G` an algebraic
group over `k` (a group scheme of finite type over `k`) and `i : H ⟶ G` a closed subgroup of
multiplicative type. If `n : N ⟶ G` represents the normalizer and `c : C ⟶ G` the
centralizer of the points of `H`, then the inclusion `f : C ⟶ N` with `f ≫ n = c` is an open
immersion. Equivalently, `N_G(H)° = C_G(H)°`. -/
def MultiplicativeTypeCentralizerOpenStatement : Prop :=
  ∀ (k : Type u) [Field k] (G H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G),
    LocallyOfFiniteType G.X.hom → QuasiCompact G.X.hom →
    IsMultiplicativeType H → IsClosedSubgroup i →
      ∀ (N C : GroupScheme (Spec (CommRingCat.of k))) (n : N ⟶ G) (c : C ⟶ G) (f : C ⟶ N),
        (SubgroupFunctor.range i).normalizer.IsRepresentedBy n →
        (SubgroupFunctor.range i).centralizer.IsRepresentedBy c →
        f ≫ n = c → IsOpenImmersion f.hom.hom.left

end Langlands.GroupScheme
