import Langlands.Representation.Classification.TadicSpehHeads
import Langlands.Representation.Classification.SegmentLinkageOrientationProof

/-! Arithmetic separation of the segment rows in opposite nonzero complementary twists. -/

namespace Langlands.Classification

open PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- Twice a nonzero exponent in the complementary interval is not integral. -/
theorem twice_complementary_exponent_ne_int {α : ℝ}
    (hα : α ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) (hα0 : α ≠ 0) (m : ℤ) :
    2 * α ≠ (m : ℝ) := by
  intro h
  have hmlo : (-1 : ℤ) < m := by
    exact_mod_cast (show (-1 : ℝ) < (m : ℝ) by linarith [hα.1])
  have hmhi : m < (1 : ℤ) := by
    exact_mod_cast (show (m : ℝ) < (1 : ℝ) by linarith [hα.2])
  have hm : m = 0 := by omega
  subst m
  apply hα0
  norm_num at h
  linarith

/-- Segment bases differing by a nonintegral real twist cannot be linked. -/
theorem not_isLinked_of_nonintegral_base_twists
    (ρ : T.CuspidalDatum.{uV,uF}) (Δ Γ : T.Segment.{uV,uF}) (s t : ℝ)
    (hΔ : Δ.base = ρ.twist s) (hΓ : Γ.base = ρ.twist t)
    (hsep : ∀ m : ℤ, s - t ≠ (m : ℝ)) : ¬ Δ.IsLinked Γ := by
  intro h
  rcases h.precedes_or_precedes with h | h
  · obtain ⟨m, _, hm⟩ := h.2
    rw [hΔ, hΓ, CuspidalDatum.twist_twist] at hm
    have ht := cuspidalDatum_twist_injective ρ hm
    apply hsep (-(m : ℤ))
    push_cast
    linarith
  · obtain ⟨m, _, hm⟩ := h.2
    rw [hΔ, hΓ, CuspidalDatum.twist_twist] at hm
    have ht := cuspidalDatum_twist_injective ρ hm
    apply hsep (m : ℤ)
    push_cast
    linarith

/-- No row of one complementary twist links to a row of the opposite twist. -/
theorem not_isLinked_complementary_segment_rows
    (Δ : T.Segment.{uV,uF}) (c α : ℝ) (i j : ℤ)
    (hα : α ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) (hα0 : α ≠ 0) :
    ¬ (Δ.twist (c - (i : ℝ) + α)).IsLinked
      (Δ.twist (c - (j : ℝ) - α)) := by
  apply not_isLinked_of_nonintegral_base_twists Δ.base _ _
    (c - (i : ℝ) + α) (c - (j : ℝ) - α) rfl rfl
  intro m hm
  apply twice_complementary_exponent_ne_int hα hα0 (m + i - j)
  push_cast
  linarith

end Langlands.Classification
