import Langlands.Representation.Aubert.MultisegmentRankOrder

/-!
# Rank-order rigidity for multisegments of a common length

These internal combinatorial lemmas isolate the segment-length obstruction used
in the neighboring Speh product argument.
-/

noncomputable section

namespace Langlands.PadicField.TopologicalData.Multisegment

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- Inclusion and equality of cuspidal content force equality of multisegments. -/
theorem eq_of_le_of_cuspidalContent_eq {a b : Multisegment.{uV, uF} T}
    (hab : a ≤ b) (hcontent : a.cuspidalContent = b.cuspidalContent) : a = b := by
  obtain ⟨c, rfl⟩ := Multiset.le_iff_exists_add.mp hab
  have hcard := congrArg Multiset.card hcontent
  rw [cuspidalContent_add, Multiset.card_add] at hcard
  have hc : Multiset.card c = 0 := by
    have := card_le_card_cuspidalContent c
    omega
  simp [Multiset.card_eq_zero.mp hc]

/-- A rank-lower multisegment with no longer segments equals a multisegment
whose segments all have the common length `l`. -/
theorem RankLE.eq_of_uniform_length {a b : Multisegment.{uV, uF} T} {l : ℕ}
    (hab : RankLE b a)
    (ha : ∀ Δ ∈ a, Δ.length = l)
    (hb : ∀ Δ ∈ b, Δ.length ≤ l) : b = a := by
  classical
  apply (eq_of_le_of_cuspidalContent_eq (a := a) (b := b) ?_ hab.1.symm).symm
  apply Multiset.le_iff_count.mpr
  intro Δ
  by_cases hΔ : Δ ∈ a
  · have hmaxa : ∀ Δ' ∈ a, Δ'.length ≤ Δ.length := by
      intro Δ' hΔ'
      rw [ha Δ' hΔ', ha Δ hΔ]
    have hmaxb : ∀ Δ' ∈ b, Δ'.length ≤ Δ.length := by
      intro Δ' hΔ'
      rw [ha Δ hΔ]
      exact hb Δ' hΔ'
    simpa only [containmentCount_eq_count_of_maximal Δ a hmaxa,
      containmentCount_eq_count_of_maximal Δ b hmaxb] using hab.2 Δ
  · simp [Multiset.count_eq_zero_of_notMem hΔ]

/-- A distinct rank-lower multisegment has a segment longer than the common
length of the original multisegment. -/
theorem RankLE.exists_longer_segment {a b : Multisegment.{uV, uF} T} {l : ℕ}
    (hab : RankLE b a) (ha : ∀ Δ ∈ a, Δ.length = l) (hne : b ≠ a) :
    ∃ Δ ∈ b, l < Δ.length := by
  by_contra h
  push Not at h
  exact hne (hab.eq_of_uniform_length ha h)

end Langlands.PadicField.TopologicalData.Multisegment
