import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessStatement
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-! # Integral coordinates on a cuspidal twist line -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace CuspidalDatum

/-- Freeness of integral twists makes the integral orbit map injective. -/
theorem integralTwist_injective
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    (ρ : CuspidalDatum.{uV, uF} T) :
    Function.Injective (fun k : ℤ => ρ.twist (k : ℝ)) := by
  intro i j hij
  have h := congrArg (fun σ : CuspidalDatum.{uV, uF} T => σ.twist (-(j : ℝ))) hij
  have ht : ρ.twist ((i - j : ℤ) : ℝ) = ρ := by
    simpa only [twist_twist, Int.cast_sub, neg_add_cancel, twist_zero,
      neg_add_eq_sub] using h
  have hz := (hfree ρ (i - j)).mp ht
  omega

end CuspidalDatum

namespace Segment

/-- The actual segment has endpoints `a` and `b` on the integral twist line
through `ρ`. The upper endpoint is inclusive. -/
def HasIntegralCoordinates (Δ : Segment.{uV, uF} T)
    (ρ : CuspidalDatum.{uV, uF} T) (a b : ℤ) : Prop :=
  Δ.base = ρ.twist (a : ℝ) ∧ b = a + (Δ.length : ℤ) - 1

theorem HasIntegralCoordinates.lower_le_upper
    {Δ : Segment.{uV, uF} T} {ρ : CuspidalDatum.{uV, uF} T} {a b : ℤ}
    (h : Δ.HasIntegralCoordinates ρ a b) : a ≤ b := by
  have := Δ.length_pos
  have := h.2
  omega

theorem hasIntegralCoordinates_self (Δ : Segment.{uV, uF} T) :
    Δ.HasIntegralCoordinates Δ.base 0 ((Δ.length : ℤ) - 1) := by
  simp [HasIntegralCoordinates]

theorem HasIntegralCoordinates.member_eq
    {Δ : Segment.{uV, uF} T} {ρ : CuspidalDatum.{uV, uF} T} {a b : ℤ}
    (h : Δ.HasIntegralCoordinates ρ a b) (i : ℕ) :
    Δ.member i = ρ.twist ((a + i : ℤ) : ℝ) := by
  simp only [member, h.1, CuspidalDatum.twist_twist, Int.cast_add, Int.cast_natCast]
  rw [add_comm]

theorem HasIntegralCoordinates.mem_support_iff
    {Δ : Segment.{uV, uF} T} {ρ σ : CuspidalDatum.{uV, uF} T} {a b : ℤ}
    (h : Δ.HasIntegralCoordinates ρ a b) :
    σ ∈ Δ.support ↔ ∃ k : ℤ, a ≤ k ∧ k ≤ b ∧ ρ.twist (k : ℝ) = σ := by
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨a + i, by omega, by have := h.2; omega, (h.member_eq i).symm⟩
  · rintro ⟨k, hak, hkb, rfl⟩
    refine ⟨(k - a).toNat, ?_, ?_⟩
    · have hcast : ((k - a).toNat : ℤ) = k - a := Int.toNat_of_nonneg (by omega)
      have := h.2
      omega
    · rw [h.member_eq]
      congr 1
      norm_cast
      rw [Int.toNat_of_nonneg (by omega)]
      omega

theorem HasIntegralCoordinates.twist_mem_support_iff
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {Δ : Segment.{uV, uF} T} {ρ : CuspidalDatum.{uV, uF} T} {a b k : ℤ}
    (h : Δ.HasIntegralCoordinates ρ a b) :
    ρ.twist (k : ℝ) ∈ Δ.support ↔ a ≤ k ∧ k ≤ b := by
  rw [h.mem_support_iff]
  constructor
  · rintro ⟨j, haj, hjb, heq⟩
    exact (ρ.integralTwist_injective hfree heq) ▸ ⟨haj, hjb⟩
  · exact fun ⟨hak, hkb⟩ => ⟨k, hak, hkb, rfl⟩

/-- The segment on a nonempty closed integral interval. -/
def ofIntegralInterval (ρ : CuspidalDatum.{uV, uF} T) (a b : ℤ) (hab : a ≤ b) :
    Segment.{uV, uF} T where
  base := ρ.twist (a : ℝ)
  length := (b - a + 1).toNat
  length_pos := by omega

theorem ofIntegralInterval_hasIntegralCoordinates
    (ρ : CuspidalDatum.{uV, uF} T) (a b : ℤ) (hab : a ≤ b) :
    (ofIntegralInterval ρ a b hab).HasIntegralCoordinates ρ a b := by
  refine ⟨rfl, ?_⟩
  change b = a + ((b - a + 1).toNat : ℤ) - 1
  rw [Int.toNat_of_nonneg (by omega)]
  omega

/-- On one free twist line, support containment is endpoint containment. -/
theorem HasIntegralCoordinates.support_subset_iff
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {Δ Γ : Segment.{uV, uF} T} {ρ : CuspidalDatum.{uV, uF} T} {a b c d : ℤ}
    (hΔ : Δ.HasIntegralCoordinates ρ a b) (hΓ : Γ.HasIntegralCoordinates ρ c d) :
    Δ.support ⊆ Γ.support ↔ c ≤ a ∧ b ≤ d := by
  constructor
  · intro hs
    have ha := (hΓ.twist_mem_support_iff hfree).mp
      (hs ((hΔ.twist_mem_support_iff hfree).mpr ⟨le_refl _, hΔ.lower_le_upper⟩))
    have hb := (hΓ.twist_mem_support_iff hfree).mp
      (hs ((hΔ.twist_mem_support_iff hfree).mpr ⟨hΔ.lower_le_upper, le_refl _⟩))
    exact ⟨ha.1, hb.2⟩
  · rintro ⟨hca, hbd⟩ σ hσ
    obtain ⟨k, hak, hkb, rfl⟩ := hΔ.mem_support_iff.mp hσ
    exact (hΓ.twist_mem_support_iff hfree).mpr ⟨by omega, by omega⟩

/-- Support equality determines both endpoints on one free twist line. -/
theorem HasIntegralCoordinates.support_eq_iff
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {Δ Γ : Segment.{uV, uF} T} {ρ : CuspidalDatum.{uV, uF} T} {a b c d : ℤ}
    (hΔ : Δ.HasIntegralCoordinates ρ a b) (hΓ : Γ.HasIntegralCoordinates ρ c d) :
    Δ.support = Γ.support ↔ a = c ∧ b = d := by
  rw [Set.Subset.antisymm_iff, hΔ.support_subset_iff hfree hΓ,
    hΓ.support_subset_iff hfree hΔ]
  omega

/-- Every segment whose base lies on the line has integral coordinates there. -/
theorem hasIntegralCoordinates_of_base_mem
    {Δ Γ : Segment.{uV, uF} T} {ρ : CuspidalDatum.{uV, uF} T} {a b : ℤ}
    (hΓ : Γ.HasIntegralCoordinates ρ a b) (hbase : Δ.base ∈ Γ.support) :
    ∃ c d : ℤ, Δ.HasIntegralCoordinates ρ c d := by
  obtain ⟨c, _, _, hc⟩ := hΓ.mem_support_iff.mp hbase
  exact ⟨c, c + Δ.length - 1, hc.symm, rfl⟩

/-- Under integral twist freeness, the support set determines the segment. -/
theorem eq_of_support_eq
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {Δ Γ : Segment.{uV, uF} T} (hs : Δ.support = Γ.support) : Δ = Γ := by
  have hΔ := Δ.hasIntegralCoordinates_self
  obtain ⟨c, d, hΓ⟩ := hasIntegralCoordinates_of_base_mem hΔ
    (hs.symm ▸ Γ.base_mem_support)
  obtain ⟨hc, hd⟩ := (hΔ.support_eq_iff hfree hΓ).mp hs
  have hbase : Δ.base = Γ.base := by
    simpa [← hc] using hΓ.1.symm
  have hlen : Δ.length = Γ.length := by
    have := hΓ.2
    have := hΔ.2
    omega
  cases Δ
  cases Γ
  simp_all

end Segment

end Langlands.PadicField.TopologicalData
