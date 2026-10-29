import Langlands.Representation.Classification.SegmentInitialTruncationOrderStatement
import Langlands.Representation.Classification.SegmentIntervalLinkage

/-! # Initial truncation preserves supplied nonprecedence orders -/

namespace Langlands.Classification

universe uF uV

open PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- If the surviving truncation has integral coordinates `[a,b]`, the original
segment has coordinates `[a,b+1]` on the same twist line. -/
private theorem coordinates_of_dropLast
    {Δ Δ' : Segment.{uV, uF} T} {ρ : CuspidalDatum.{uV, uF} T} {a b : ℤ}
    (hdrop : Δ.dropLast = some Δ')
    (hcoord : Δ'.HasIntegralCoordinates ρ a b) :
    Δ.HasIntegralCoordinates ρ a (b + 1) := by
  by_cases h : 1 < Δ.length
  · rw [Δ.dropLast_of_one_lt h] at hdrop
    have heq := Option.some.inj hdrop
    subst Δ'
    refine ⟨hcoord.1, ?_⟩
    have hend := hcoord.2
    change b = a + ((Δ.length - 1 : ℕ) : ℤ) - 1 at hend
    omega
  · simp [Segment.dropLast, h] at hdrop

/-- Deleting the last position of each segment creates no new precedence
between surviving truncations and preserves every supplied nonprecedence list
order. -/
theorem segmentInitialTruncationOrder :
    SegmentInitialTruncationOrder.{uF, uV} F T := by
  intro hfree
  have hpair : ∀ Δ Γ Δ' Γ' : Segment.{uV, uF} T,
      Δ.dropLast = some Δ' → Γ.dropLast = some Γ' →
      Δ'.Precedes Γ' → Δ.Precedes Γ := by
    intro Δ Γ Δ' Γ' hΔ hΓ hprec
    have hcoordΔ := Δ'.hasIntegralCoordinates_self
    obtain ⟨c, d, hcoordΓ⟩ := hcoordΔ.of_precedes_right hprec
    have hinter := (hcoordΔ.precedes_iff hfree hcoordΓ).mp hprec
    apply (coordinates_of_dropLast F T hΔ hcoordΔ).precedes_of_intervalPrecedes
      hfree (coordinates_of_dropLast F T hΓ hcoordΓ)
    rcases hinter with ⟨hac, hcb, hbd⟩
    exact ⟨hac, by omega, by omega⟩
  refine ⟨hpair, ?_⟩
  intro l hl
  change l.Pairwise (fun Δ Γ => ¬ Δ.Precedes Γ) at hl
  change (l.filterMap Segment.dropLast).Pairwise (fun Δ Γ => ¬ Δ.Precedes Γ)
  apply List.Pairwise.filterMap Segment.dropLast ?_ hl
  intro Δ Γ hnot Δ' hΔ Γ' hΓ hprec
  exact hnot (hpair Δ Γ Δ' Γ' (by simpa only [Option.mem_def] using hΔ)
    (by simpa only [Option.mem_def] using hΓ) hprec)

end Langlands.Classification
