import Mathlib.GroupTheory.Index

namespace Langlands.Ramification.HerbrandBridge

/-- The second isomorphism theorem for indices: for a normal subgroup `N`, the index of `H` in
`N ⊔ H` is the index of `H ∩ N` in `N`. -/
theorem relIndex_normal_sup {G : Type*} [Group G] (H N : Subgroup G) [N.Normal] :
    H.relIndex (N ⊔ H) = H.relIndex N := by
  let e := Subgroup.quotientSubgroupOfEmbeddingOfLE H (le_sup_left : N ≤ N ⊔ H)
  symm
  apply Nat.card_congr (Equiv.ofBijective e ⟨e.injective, ?_⟩)
  intro q
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨n, hn, h, hh, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  refine ⟨QuotientGroup.mk (⟨n, hn⟩ : N), ?_⟩
  rw [show e (QuotientGroup.mk (⟨n, hn⟩ : N)) =
    QuotientGroup.mk (Subgroup.inclusion le_sup_left ⟨n, hn⟩) from rfl, QuotientGroup.eq]
  change n⁻¹ * (n * h) ∈ H
  simpa using hh

end Langlands.Ramification.HerbrandBridge
