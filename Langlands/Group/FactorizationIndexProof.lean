import Langlands.Group.FactorizationIndexStatement

/-! # Proof of the compatible factorization index formula -/

noncomputable section

universe u

namespace Langlands.Group

private theorem quotientImages_isComplement
    {G : Type u} [Group G] (A B N : Subgroup G) [N.Normal]
    (hAB : A.IsComplement' B)
    (hN : (A.subgroupOf N).IsComplement' (B.subgroupOf N)) :
    (A.map (QuotientGroup.mk' N)).IsComplement' (B.map (QuotientGroup.mk' N)) := by
  let q := QuotientGroup.mk' N
  have hd : Disjoint (A.map q) (B.map q) := by
    rw [disjoint_iff_inf_le]
    rintro x ⟨hxA, hxB⟩
    obtain ⟨a, ha, hax⟩ := hxA
    obtain ⟨b, hb, hbx⟩ := hxB
    have hn : a * b⁻¹ ∈ N := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (a * b⁻¹) = 1
      simp only [map_mul, map_inv, hax, hbx, mul_inv_cancel]
    obtain ⟨⟨c, d⟩, hcd⟩ := hN.2 ⟨a * b⁻¹, hn⟩
    have heq :
        (⟨⟨a, ha⟩, ⟨b⁻¹, B.inv_mem hb⟩⟩ : A × B) =
          ⟨⟨(c : N), c.property⟩, ⟨(d : N), d.property⟩⟩ := by
      apply hAB.1
      exact (congrArg (fun n : N => (n : G)) hcd).symm
    have hac : a = (c : N) :=
      congrArg (fun t : A × B => (t.1 : G)) heq
    have haN : a ∈ N := hac ▸ (c : N).property
    change x = 1
    rw [← hax]
    exact (QuotientGroup.eq_one_iff a).mpr haN
  refine ⟨Subgroup.mul_injective_of_disjoint hd, ?_⟩
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
  obtain ⟨⟨a, b⟩, hab⟩ := hAB.2 g
  refine ⟨⟨⟨q a, Subgroup.mem_map.mpr ⟨a, a.property, rfl⟩⟩,
    ⟨q b, Subgroup.mem_map.mpr ⟨b, b.property, rfl⟩⟩⟩, ?_⟩
  change q a * q b = q g
  rw [← map_mul]
  exact congrArg q hab

/-- The exact factorization index statement, at every universe. -/
theorem factorizationIndex : FactorizationIndexStatement.{u} := by
  intro G _ A B N _ hAB hN
  have h := (quotientImages_isComplement A B N hAB hN).card_mul_card
  rw [← Subgroup.relIndex_ker, ← Subgroup.relIndex_ker,
    QuotientGroup.ker_mk'] at h
  exact h.symm

end Langlands.Group
