import Langlands.Representation.Classification.SegmentLinkageOrientationStatement

namespace Langlands.PadicField.TopologicalData.Segment

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

private theorem support_subset_of_base_eq_length_le
    {Δ Γ : T.Segment.{uV,uF}} (hb : Δ.base = Γ.base) (hl : Δ.length ≤ Γ.length) :
    Δ.support ⊆ Γ.support := by
  rintro ρ ⟨i, hi, rfl⟩
  exact ⟨i, lt_of_lt_of_le hi hl, by simp only [member, hb]⟩

/-- Linked segments have a precedence relation in at least one direction. -/
theorem IsLinked.precedes_or_precedes {Δ Γ : T.Segment.{uV,uF}}
    (h : Δ.IsLinked Γ) : Δ.Precedes Γ ∨ Γ.Precedes Δ := by
  have hbase : Δ.base ≠ Γ.base := by
    intro hb
    rcases le_total Δ.length Γ.length with hl | hl
    · exact h.1 (support_subset_of_base_eq_length_le hb hl)
    · exact h.2.1 (support_subset_of_base_eq_length_le hb.symm hl)
  obtain ⟨U, hU⟩ := h.2.2
  have hΔ : Δ.base ∈ U.support := by
    rw [hU]
    exact Or.inl Δ.base_mem_support
  have hΓ : Γ.base ∈ U.support := by
    rw [hU]
    exact Or.inr Γ.base_mem_support
  obtain ⟨a, _, ha⟩ := hΔ
  obtain ⟨b, _, hb⟩ := hΓ
  have hab : a ≠ b := by
    intro he
    apply hbase
    rw [← ha, ← hb, he]
  rcases lt_or_gt_of_ne hab with hab | hba
  · left
    refine ⟨h, b - a, Nat.sub_pos_of_lt hab, ?_⟩
    rw [← ha, ← hb]
    simp only [member, CuspidalDatum.twist_twist]
    congr 1
    rw [Nat.cast_sub (Nat.le_of_lt hab)]
    ring
  · right
    refine ⟨h.symm, a - b, Nat.sub_pos_of_lt hba, ?_⟩
    rw [← ha, ← hb]
    simp only [member, CuspidalDatum.twist_twist]
    congr 1
    rw [Nat.cast_sub (Nat.le_of_lt hba)]
    ring

end Langlands.PadicField.TopologicalData.Segment

namespace Langlands.Classification

universe uF uV

/-- The finite support definitions orient every linked pair of segments. -/
theorem segmentLinkageOrientation
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    SegmentLinkageOrientation.{uF,uV} F T := by
  intro Δ Γ h
  exact h.precedes_or_precedes

end Langlands.Classification
