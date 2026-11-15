import Langlands.GroupScheme.Reductive.Semisimple
import Mathlib.FieldTheory.Perfect

/-! # Semisimple groups and commutative normal subgroups: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Semisimple groups have no commutative normal subgroup varieties** (Milne,
*Algebraic Groups* (2017), Proposition 19.3). Let `G` be a smooth connected affine group
scheme over a field `k`. If `G` is semisimple, then every smooth connected commutative
normal closed subgroup of `G` is trivial. Conversely, if `k` is perfect and every such
subgroup is trivial, then `G` is semisimple.

Semisimple is the Library's `IsSemisimple`: connected reductive with finite
scheme-theoretic centre. A subgroup `j : H ⟶ G` is commutative when the group law of
`H` is commutative (`IsCommMonObj H.X`). -/
def SemisimpleCommutativeNormalSubgroupStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    Smooth G.X.hom → IsAffineHom G.X.hom → ConnectedSpace G.X.left →
      let NoCommutativeNormal : Prop :=
        ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
          IsClosedSubgroup j → Smooth H.X.hom → ConnectedSpace H.X.left →
            IsCommMonObj H.X → (SubgroupFunctor.range j).IsNormal →
              SubgroupFunctor.range j = ⊥
      (IsSemisimple G → NoCommutativeNormal) ∧
      (PerfectField k → NoCommutativeNormal → IsSemisimple G)

end Langlands.GroupScheme
