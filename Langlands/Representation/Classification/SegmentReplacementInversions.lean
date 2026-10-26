import Langlands.Representation.Classification.SegmentIntervalLinkage
import Langlands.Combinatorics.RelationInversions

/-! # Inversion decrease for union/intersection replacement -/

noncomputable section

open scoped Classical

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace Segment

open Langlands.Combinatorics

/-- The actual union and optional intersection supports. An empty intersection
is omitted from the replacement list. -/
def IsUnionIntersectionReplacement (Δ Γ U : Segment.{uV, uF} T)
    (I : Option (Segment.{uV, uF} T)) : Prop :=
  U.support = Δ.support ∪ Γ.support ∧
    match I with
    | none => Δ.support ∩ Γ.support = ∅
    | some J => J.support = Δ.support ∩ Γ.support

theorem HasIntegralCoordinates.support_inter_eq
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {Δ Γ : Segment.{uV, uF} T} {ρ : CuspidalDatum.{uV, uF} T} {a b c d : ℤ}
    (hΔ : Δ.HasIntegralCoordinates ρ a b) (hΓ : Γ.HasIntegralCoordinates ρ c d)
    (hac : a ≤ c) (hbd : b ≤ d) (hcb : c ≤ b) :
    (ofIntegralInterval ρ c b hcb).support = Δ.support ∩ Γ.support := by
  ext σ
  rw [(ofIntegralInterval_hasIntegralCoordinates ρ c b hcb).mem_support_iff,
    Set.mem_inter_iff, hΔ.mem_support_iff, hΓ.mem_support_iff]
  constructor
  · rintro ⟨k, hck, hkb, hk⟩
    exact ⟨⟨k, by omega, hkb, hk⟩, ⟨k, hck, by omega, hk⟩⟩
  · rintro ⟨⟨k, hak, hkb, hk⟩, ⟨l, hcl, hld, hl⟩⟩
    have hkl := ρ.integralTwist_injective hfree (hk.trans hl.symm)
    exact ⟨k, by omega, hkb, hk⟩

theorem IsUnionIntersectionReplacement.coordinates
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {Δ Γ U : Segment.{uV, uF} T} {I : Option (Segment.{uV, uF} T)}
    (hs : IsUnionIntersectionReplacement Δ Γ U I) (hp : Δ.Precedes Γ) :
    ∃ (ρ : CuspidalDatum.{uV, uF} T) (a b c d : ℤ),
      Δ.HasIntegralCoordinates ρ a b ∧ Γ.HasIntegralCoordinates ρ c d ∧
        IntervalPrecedes a b c d ∧ U.HasIntegralCoordinates ρ a d ∧
          ∀ J, I = some J → J.HasIntegralCoordinates ρ c b := by
  have hΔ := Δ.hasIntegralCoordinates_self
  obtain ⟨c, d, hΓ⟩ := hΔ.of_precedes_right hp
  have hends := (hΔ.precedes_iff hfree hΓ).mp hp
  obtain ⟨hac, hcb, hbd⟩ := hends
  have hUeq := eq_of_support_eq hfree
    (hs.1.trans (hΔ.support_union_eq hΓ (by omega) hcb (by omega)).symm)
  refine ⟨Δ.base, 0, (Δ.length : ℤ) - 1, c, d, hΔ, hΓ,
    ⟨hac, hcb, hbd⟩, ?_, ?_⟩
  · rw [hUeq]
    exact ofIntegralInterval_hasIntegralCoordinates _ _ _ _
  · intro J hIJ
    have hJ : J.support = Δ.support ∩ Γ.support := by
      simpa only [IsUnionIntersectionReplacement, hIJ] using hs.2
    have hm := J.base_mem_support
    rw [hJ] at hm
    obtain ⟨k, hak, hkb, hk⟩ := hΔ.mem_support_iff.mp hm.1
    have hck := (hΓ.twist_mem_support_iff hfree).mp (hk.symm ▸ hm.2)
    have hnonempty : c ≤ (Δ.length : ℤ) - 1 := by omega
    have hJeq := eq_of_support_eq hfree
      (hJ.trans (hΔ.support_inter_eq hfree hΓ (by omega) (by omega) hnonempty).symm)
    rw [hJeq]
    exact ofIntegralInterval_hasIntegralCoordinates _ _ _ _

private theorem interval_pairCount_left
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {Δ Γ U J Θ : Segment.{uV, uF} T} {ρ : CuspidalDatum.{uV, uF} T}
    {a b c d x y : ℤ}
    (hΔ : Δ.HasIntegralCoordinates ρ a b) (hΓ : Γ.HasIntegralCoordinates ρ c d)
    (hU : U.HasIntegralCoordinates ρ a d) (hJ : J.HasIntegralCoordinates ρ c b)
    (hΘ : Θ.HasIntegralCoordinates ρ x y) (hp : IntervalPrecedes a b c d) :
    relationPairCount Precedes [Θ] [U, J] ≤ relationPairCount Precedes [Θ] [Δ, Γ] := by
  classical
  simp only [relationPairCount, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero, hΘ.precedes_iff hfree hU, hΘ.precedes_iff hfree hJ,
    hΘ.precedes_iff hfree hΔ, hΘ.precedes_iff hfree hΓ]
  unfold IntervalPrecedes at *
  split_ifs <;> omega

private theorem interval_pairCount_right
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {Δ Γ U J Θ : Segment.{uV, uF} T} {ρ : CuspidalDatum.{uV, uF} T}
    {a b c d x y : ℤ}
    (hΔ : Δ.HasIntegralCoordinates ρ a b) (hΓ : Γ.HasIntegralCoordinates ρ c d)
    (hU : U.HasIntegralCoordinates ρ a d) (hJ : J.HasIntegralCoordinates ρ c b)
    (hΘ : Θ.HasIntegralCoordinates ρ x y) (hp : IntervalPrecedes a b c d) :
    relationPairCount Precedes [U, J] [Θ] ≤ relationPairCount Precedes [Δ, Γ] [Θ] := by
  classical
  simp only [relationPairCount, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero, hU.precedes_iff hfree hΘ, hJ.precedes_iff hfree hΘ,
    hΔ.precedes_iff hfree hΘ, hΓ.precedes_iff hfree hΘ]
  unfold IntervalPrecedes at *
  split_ifs <;> omega

/-- Every segment to the left has no more outgoing inversions after replacement. -/
theorem IsUnionIntersectionReplacement.pairCount_left_le
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {Δ Γ U : Segment.{uV, uF} T} {I : Option (Segment.{uV, uF} T)}
    (hs : IsUnionIntersectionReplacement Δ Γ U I) (hp : Δ.Precedes Γ)
    (Θ : Segment.{uV, uF} T) :
    relationPairCount Precedes [Θ] (U :: I.toList) ≤
      relationPairCount Precedes [Θ] [Δ, Γ] := by
  classical
  obtain ⟨ρ, a, b, c, d, hΔ, hΓ, hends, hU, hI⟩ := hs.coordinates hfree hp
  cases I with
  | none =>
    simp only [Option.toList_none]
    by_cases ht : Θ.Precedes U
    · obtain ⟨x, y, hΘ⟩ := hU.of_precedes_left ht
      simp only [relationPairCount, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nat.add_zero, hΘ.precedes_iff hfree hU,
        hΘ.precedes_iff hfree hΔ, hΘ.precedes_iff hfree hΓ]
      have ht' := (hΘ.precedes_iff hfree hU).mp ht
      unfold IntervalPrecedes at *
      split_ifs <;> omega
    · simp [relationPairCount, ht]
  | some J =>
    simp only [Option.toList_some]
    have hJ := hI J rfl
    by_cases ht : Θ.Precedes U ∨ Θ.Precedes J
    · obtain ⟨x, y, hΘ⟩ : ∃ x y : ℤ, Θ.HasIntegralCoordinates ρ x y := by
        rcases ht with ht | ht
        · exact hU.of_precedes_left ht
        · exact hJ.of_precedes_left ht
      exact interval_pairCount_left hfree hΔ hΓ hU hJ hΘ hends
    · have hu : ¬ Θ.Precedes U := fun h => ht (Or.inl h)
      have hj : ¬ Θ.Precedes J := fun h => ht (Or.inr h)
      simp [relationPairCount, hu, hj]

/-- Every segment to the right has no more incoming inversions after replacement. -/
theorem IsUnionIntersectionReplacement.pairCount_right_le
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {Δ Γ U : Segment.{uV, uF} T} {I : Option (Segment.{uV, uF} T)}
    (hs : IsUnionIntersectionReplacement Δ Γ U I) (hp : Δ.Precedes Γ)
    (Θ : Segment.{uV, uF} T) :
    relationPairCount Precedes (U :: I.toList) [Θ] ≤
      relationPairCount Precedes [Δ, Γ] [Θ] := by
  classical
  obtain ⟨ρ, a, b, c, d, hΔ, hΓ, hends, hU, hI⟩ := hs.coordinates hfree hp
  cases I with
  | none =>
    simp only [Option.toList_none]
    by_cases ht : U.Precedes Θ
    · obtain ⟨x, y, hΘ⟩ := hU.of_precedes_right ht
      simp only [relationPairCount, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nat.add_zero, hU.precedes_iff hfree hΘ,
        hΔ.precedes_iff hfree hΘ, hΓ.precedes_iff hfree hΘ]
      have ht' := (hU.precedes_iff hfree hΘ).mp ht
      unfold IntervalPrecedes at *
      split_ifs <;> omega
    · simp [relationPairCount, ht]
  | some J =>
    simp only [Option.toList_some]
    have hJ := hI J rfl
    by_cases ht : U.Precedes Θ ∨ J.Precedes Θ
    · obtain ⟨x, y, hΘ⟩ : ∃ x y : ℤ, Θ.HasIntegralCoordinates ρ x y := by
        rcases ht with ht | ht
        · exact hU.of_precedes_right ht
        · exact hJ.of_precedes_right ht
      exact interval_pairCount_right hfree hΔ hΓ hU hJ hΘ hends
    · have hu : ¬ U.Precedes Θ := fun h => ht (Or.inl h)
      have hj : ¬ J.Precedes Θ := fun h => ht (Or.inr h)
      simp [relationPairCount, hu, hj]

theorem IsUnionIntersectionReplacement.inversions_eq_zero
    {Δ Γ U : Segment.{uV, uF} T} {I : Option (Segment.{uV, uF} T)}
    (hs : IsUnionIntersectionReplacement Δ Γ U I) :
    relationInversions Precedes (U :: I.toList) = 0 := by
  classical
  cases I with
  | none => simp
  | some J =>
    have hJ : J.support = Δ.support ∩ Γ.support := hs.2
    have hsub : J.support ⊆ U.support := by
      rw [hJ, hs.1]
      exact fun _ h => Or.inl h.1
    have hnot : ¬ U.Precedes J := fun h => h.1.2.1 hsub
    simp [relationPairCount, hnot]

/-- Union/intersection replacement strictly decreases the full positional count,
with arbitrary outside lists and all their repeated occurrences retained. -/
theorem IsUnionIntersectionReplacement.inversions_replace_lt
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {Δ Γ U : Segment.{uV, uF} T} {I : Option (Segment.{uV, uF} T)}
    (hs : IsUnionIntersectionReplacement Δ Γ U I) (hp : Δ.Precedes Γ)
    (l r : List (Segment.{uV, uF} T)) :
    relationInversions Precedes (l ++ (U :: I.toList) ++ r) <
      relationInversions Precedes (l ++ [Δ, Γ] ++ r) := by
  classical
  apply relationInversions_replace_lt
  · rw [hs.inversions_eq_zero]
    simp [relationPairCount, hp]
  · exact fun Θ _ => hs.pairCount_left_le hfree hp Θ
  · exact fun Θ _ => hs.pairCount_right_le hfree hp Θ

end Segment

end Langlands.PadicField.TopologicalData
