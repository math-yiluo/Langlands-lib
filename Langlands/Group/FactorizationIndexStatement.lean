import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Indices from a compatible exact subgroup factorization -/

universe u

namespace Langlands.Group

/-- A normal subgroup compatible with an exact two-factor decomposition
has index equal to the product of its indices in the two factors. -/
def FactorizationIndexStatement : Prop :=
  ∀ (G : Type u) [Group G] (A B N : Subgroup G) [N.Normal],
    A.IsComplement' B →
    (A.subgroupOf N).IsComplement' (B.subgroupOf N) →
    N.index = N.relIndex A * N.relIndex B

end Langlands.Group
