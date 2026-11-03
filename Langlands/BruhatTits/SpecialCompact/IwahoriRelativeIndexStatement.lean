import Langlands.BruhatTits.SpecialCompact.SmallSubgroupPredicates
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Relative indices from compatible Iwahori factorizations -/

universe u

namespace Langlands.BruhatTits.SpecialCompact

/-- The index of a possibly nonnormal Iwahori-factorized subgroup is the
product of the three intersection indices, provided there is a compatible
common normal subgroup of finite index. -/
def IwahoriRelativeIndexStatement : Prop :=
  ∀ (G : Type u) [Group G] (K J H M U V P : Subgroup G),
    H ≤ J → J ≤ K →
    (H.subgroupOf K).Normal →
    H.relIndex K ≠ 0 →
    M ≤ P → U ≤ P → Disjoint V P →
    HasIwahoriIntersectionDecomposition K M U V →
    HasIwahoriIntersectionDecomposition J M U V →
    HasIwahoriIntersectionDecomposition H M U V →
    J.relIndex K =
      J.relIndex (K ⊓ V) * J.relIndex (K ⊓ M) * J.relIndex (K ⊓ U)

end Langlands.BruhatTits.SpecialCompact
