import Langlands.Representation.Classification.SegmentIntegralCoordinates

/-! # Precedence in integral segment coordinates -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace Segment

/-- The inclusive endpoints of two intervals have the precedence configuration. -/
def IntervalPrecedes (a b c d : ℤ) : Prop :=
  a < c ∧ c ≤ b + 1 ∧ b < d

theorem HasIntegralCoordinates.of_precedes_right
    {Δ Γ : Segment.{uV, uF} T} {ρ : CuspidalDatum.{uV, uF} T} {a b : ℤ}
    (hΔ : Δ.HasIntegralCoordinates ρ a b) (h : Δ.Precedes Γ) :
    ∃ c d : ℤ, Γ.HasIntegralCoordinates ρ c d := by
  obtain ⟨k, _, hk⟩ := h.2
  refine ⟨a + k, a + k + Γ.length - 1, ?_, rfl⟩
  rw [hk, hΔ.1, CuspidalDatum.twist_twist]
  congr 1
  push_cast
  ring

theorem HasIntegralCoordinates.of_precedes_left
    {Δ Γ : Segment.{uV, uF} T} {ρ : CuspidalDatum.{uV, uF} T} {c d : ℤ}
    (hΓ : Γ.HasIntegralCoordinates ρ c d) (h : Δ.Precedes Γ) :
    ∃ a b : ℤ, Δ.HasIntegralCoordinates ρ a b := by
  obtain ⟨k, _, hk⟩ := h.2
  refine ⟨c - k, c - k + Δ.length - 1, ?_, rfl⟩
  have he := congrArg (fun σ : CuspidalDatum.{uV, uF} T => σ.twist (-(k : ℝ))) hk
  rw [CuspidalDatum.twist_twist, neg_add_cancel, CuspidalDatum.twist_zero, hΓ.1,
    CuspidalDatum.twist_twist] at he
  rw [← he]
  congr 1
  push_cast
  ring

theorem HasIntegralCoordinates.support_union_eq
    {Δ Γ : Segment.{uV, uF} T} {ρ : CuspidalDatum.{uV, uF} T} {a b c d : ℤ}
    (hΔ : Δ.HasIntegralCoordinates ρ a b) (hΓ : Γ.HasIntegralCoordinates ρ c d)
    (hac : a ≤ c) (hcb : c ≤ b + 1) (hbd : b ≤ d) :
    (ofIntegralInterval ρ a d (by have := hΔ.lower_le_upper; omega)).support =
      Δ.support ∪ Γ.support := by
  ext σ
  rw [(ofIntegralInterval_hasIntegralCoordinates ρ a d
    (by have := hΔ.lower_le_upper; omega)).mem_support_iff,
    Set.mem_union, hΔ.mem_support_iff, hΓ.mem_support_iff]
  constructor
  · rintro ⟨k, hak, hkd, hk⟩
    by_cases hkb : k ≤ b
    · exact Or.inl ⟨k, hak, hkb, hk⟩
    · exact Or.inr ⟨k, by omega, hkd, hk⟩
  · rintro (⟨k, hak, hkb, hk⟩ | ⟨k, hck, hkd, hk⟩)
    · exact ⟨k, hak, by omega, hk⟩
    · exact ⟨k, by omega, hkd, hk⟩

theorem HasIntegralCoordinates.precedes_of_intervalPrecedes
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {Δ Γ : Segment.{uV, uF} T} {ρ : CuspidalDatum.{uV, uF} T} {a b c d : ℤ}
    (hΔ : Δ.HasIntegralCoordinates ρ a b) (hΓ : Γ.HasIntegralCoordinates ρ c d)
    (h : IntervalPrecedes a b c d) : Δ.Precedes Γ := by
  obtain ⟨hac, hcb, hbd⟩ := h
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hΔ.support_subset_iff hfree hΓ]
    omega
  · rw [hΓ.support_subset_iff hfree hΔ]
    omega
  · exact ⟨ofIntegralInterval ρ a d (by have := hΔ.lower_le_upper; omega),
      hΔ.support_union_eq hΓ (by omega) hcb (by omega)⟩
  · refine ⟨(c - a).toNat, by omega, ?_⟩
    rw [hΓ.1, hΔ.1, CuspidalDatum.twist_twist]
    congr 1
    have ht : ((c - a).toNat : ℤ) = c - a := Int.toNat_of_nonneg (by omega)
    norm_cast
    omega

theorem HasIntegralCoordinates.intervalPrecedes_of_precedes
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {Δ Γ : Segment.{uV, uF} T} {ρ : CuspidalDatum.{uV, uF} T} {a b c d : ℤ}
    (hΔ : Δ.HasIntegralCoordinates ρ a b) (hΓ : Γ.HasIntegralCoordinates ρ c d)
    (h : Δ.Precedes Γ) : IntervalPrecedes a b c d := by
  obtain ⟨k, hk, he⟩ := h.2
  have hcast : c = a + k := by
    apply ρ.integralTwist_injective hfree
    simpa only [hΓ.1, hΔ.1, CuspidalDatum.twist_twist, Int.cast_add,
      Int.cast_natCast, add_comm] using he
  have hac : a < c := by omega
  have hbd : b < d := by
    have hn := h.1.1
    rw [hΔ.support_subset_iff hfree hΓ] at hn
    have hn' := h.1.2.1
    rw [hΓ.support_subset_iff hfree hΔ] at hn'
    omega
  refine ⟨hac, ?_, hbd⟩
  by_contra hgap
  obtain ⟨U, hU⟩ := h.1.2.2
  have hbase : U.base ∈ Δ.support ∪ Γ.support := hU ▸ U.base_mem_support
  obtain ⟨e, f, hcoord⟩ : ∃ e f : ℤ, U.HasIntegralCoordinates ρ e f := by
    rcases hbase with hl | hr
    · exact hasIntegralCoordinates_of_base_mem hΔ hl
    · exact hasIntegralCoordinates_of_base_mem hΓ hr
  have hsubΔ : Δ.support ⊆ U.support := by
    rw [hU]
    exact Set.subset_union_left
  have hsubΓ : Γ.support ⊆ U.support := by
    rw [hU]
    exact Set.subset_union_right
  have hboundsΔ := (hΔ.support_subset_iff hfree hcoord).mp hsubΔ
  have hboundsΓ := (hΓ.support_subset_iff hfree hcoord).mp hsubΓ
  have hm : ρ.twist ((b + 1 : ℤ) : ℝ) ∈ U.support :=
    (hcoord.twist_mem_support_iff hfree).mpr
      ⟨by have := hΔ.lower_le_upper; omega, by omega⟩
  rw [hU, Set.mem_union, hΔ.twist_mem_support_iff hfree,
    hΓ.twist_mem_support_iff hfree] at hm
  omega

/-- Precedence is exactly the strict endpoint configuration on a free twist line. -/
theorem HasIntegralCoordinates.precedes_iff
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {Δ Γ : Segment.{uV, uF} T} {ρ : CuspidalDatum.{uV, uF} T} {a b c d : ℤ}
    (hΔ : Δ.HasIntegralCoordinates ρ a b) (hΓ : Γ.HasIntegralCoordinates ρ c d) :
    Δ.Precedes Γ ↔ IntervalPrecedes a b c d :=
  ⟨hΔ.intervalPrecedes_of_precedes hfree hΓ,
    hΔ.precedes_of_intervalPrecedes hfree hΓ⟩

end Segment

end Langlands.PadicField.TopologicalData
