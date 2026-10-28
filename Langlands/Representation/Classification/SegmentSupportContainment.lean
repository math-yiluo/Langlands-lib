import Langlands.Representation.Classification.Segments

/-!
# Containment of shifted segment supports

The existing support-containment lemma is shared by the nonlinkage and
linked-head exponent proofs.
-/

namespace Langlands.PadicField.TopologicalData.Segment

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  {T : F.TopologicalData}

/-- If the base of the second segment starts `k` positions into the first and
its last index stays inside the first, its support is contained in the first. -/
theorem support_subset_of_base_shift {Δ Δ' : T.Segment.{uV, uF}} {k : ℕ}
    (hbase : Δ'.base = Δ.base.twist (k : ℝ))
    (hend : k + Δ'.length ≤ Δ.length) : Δ'.support ⊆ Δ.support := by
  rintro ρ ⟨i, hi, rfl⟩
  refine ⟨k + i, by omega, ?_⟩
  simp only [member, hbase, CuspidalDatum.twist_twist, Nat.cast_add]
  rw [add_comm]

end Langlands.PadicField.TopologicalData.Segment
