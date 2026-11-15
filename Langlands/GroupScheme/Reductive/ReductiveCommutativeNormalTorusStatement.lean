import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.Lattice
import Mathlib.FieldTheory.Perfect

/-! # Reductive groups and commutative normal subgroups: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Commutative normal subgroup varieties of reductive groups are tori** (Milne,
*Algebraic Groups* (2017), Proposition 19.12). Let `G` be a smooth connected affine group
scheme over a field `k`. If `G` is reductive, then every smooth connected commutative
normal closed subgroup of `G` is a torus. Conversely, if `k` is perfect and every such
subgroup is a torus, then `G` is reductive.

Reductive is the Library's `IsConnectedReductive`, and torus is the Library's field
predicate `IsTorus` (split after base change to some field extension). A subgroup
`j : H ⟶ G` is commutative when the group law of `H` is commutative
(`IsCommMonObj H.X`). -/
def ReductiveCommutativeNormalTorusStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    Smooth G.X.hom → IsAffineHom G.X.hom → ConnectedSpace G.X.left →
      let CommutativeNormalAreTori : Prop :=
        ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
          IsClosedSubgroup j → Smooth H.X.hom → ConnectedSpace H.X.left →
            IsCommMonObj H.X → (SubgroupFunctor.range j).IsNormal →
              IsTorus H
      (IsConnectedReductive G → CommutativeNormalAreTori) ∧
      (PerfectField k → CommutativeNormalAreTori → IsConnectedReductive G)

end Langlands.GroupScheme
