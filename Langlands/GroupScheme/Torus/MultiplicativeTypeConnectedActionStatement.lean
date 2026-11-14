import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.GroupScheme.AutomorphicAction
import Langlands.GroupScheme.Rational.Characters

/-! # Statement: connected groups act trivially on groups of multiplicative type -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Rigidity of groups of multiplicative type** (Milne, *Algebraic Groups* (2017),
Corollaries 12.37 and 12.38). Let `k` be a field, `G` a connected algebraic group over `k`
(a connected group scheme of finite type over `k`) and `H` a group of multiplicative type
over `k`.
1. Every action of `G` on `H` by group automorphisms is trivial.
2. If `H` is a closed normal subgroup of `G`, then `H` is central in `G`. -/
def MultiplicativeTypeConnectedActionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G H : GroupScheme (Spec (CommRingCat.of k))),
    LocallyOfFiniteType G.X.hom → QuasiCompact G.X.hom → ConnectedSpace G.X.left →
    IsMultiplicativeType H →
      (∀ (a : AutomorphicAction G H) (T : Over (Spec (CommRingCat.of k)))
          (g : T ⟶ G.X) (x : T ⟶ H.X), a.act g x = x) ∧
      (∀ h : H ⟶ G, IsClosedSubgroup h → (SubgroupFunctor.range h).IsNormal → IsCentral h)

end Langlands.GroupScheme
