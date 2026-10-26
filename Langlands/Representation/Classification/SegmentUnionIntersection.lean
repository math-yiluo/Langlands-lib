import Langlands.Representation.Classification.SegmentReplacementInversions

/-! Actual union/intersection segments and their length and degree bookkeeping. -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace Segment

theorem HasIntegralCoordinates.rank_eq
    {Δ : Segment.{uV, uF} T} {ρ : CuspidalDatum.{uV, uF} T} {a b : ℤ}
    (h : Δ.HasIntegralCoordinates ρ a b) : Δ.rank = ρ.rank := by
  simp only [rank, h.1, CuspidalDatum.twist_rank]

/-- Separated integral intervals have disjoint supports on a free twist line. -/
theorem HasIntegralCoordinates.support_inter_eq_empty
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {Δ Γ : Segment.{uV, uF} T} {ρ : CuspidalDatum.{uV, uF} T} {a b c d : ℤ}
    (hΔ : Δ.HasIntegralCoordinates ρ a b) (hΓ : Γ.HasIntegralCoordinates ρ c d)
    (hbc : b < c) : Δ.support ∩ Γ.support = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro σ hσ
  obtain ⟨k, _, hkb, hk⟩ := hΔ.mem_support_iff.mp hσ.1
  obtain ⟨l, hcl, _, hl⟩ := hΓ.mem_support_iff.mp hσ.2
  have hkl := ρ.integralTwist_injective hfree (hk.trans hl.symm)
  omega

/-- A preceding pair has an actual union segment and an optional actual
intersection segment. An empty intersection is omitted. -/
theorem exists_unionIntersectionReplacement
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {Δ Γ : Segment.{uV, uF} T} (hp : Δ.Precedes Γ) :
    ∃ (U : Segment.{uV, uF} T) (I : Option (Segment.{uV, uF} T)),
      IsUnionIntersectionReplacement Δ Γ U I := by
  have hΔ := Δ.hasIntegralCoordinates_self
  obtain ⟨c, d, hΓ⟩ := hΔ.of_precedes_right hp
  obtain ⟨hac, hcb, hbd⟩ := hΔ.intervalPrecedes_of_precedes hfree hΓ hp
  let U := ofIntegralInterval Δ.base 0 d (by have := hΔ.lower_le_upper; omega)
  have hU : U.support = Δ.support ∪ Γ.support :=
    hΔ.support_union_eq hΓ (by omega) hcb (by omega)
  by_cases hi : c ≤ (Δ.length : ℤ) - 1
  · exact ⟨U, some (ofIntegralInterval Δ.base c ((Δ.length : ℤ) - 1) hi),
      hU, hΔ.support_inter_eq hfree hΓ (by omega) (by omega) hi⟩
  · exact ⟨U, none, hU, hΔ.support_inter_eq_empty hfree hΓ (by omega)⟩

/-- Every actual replacement preserves the sum of segment lengths. -/
theorem IsUnionIntersectionReplacement.length_sum
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {Δ Γ U : Segment.{uV, uF} T} {I : Option (Segment.{uV, uF} T)}
    (hs : IsUnionIntersectionReplacement Δ Γ U I) (hp : Δ.Precedes Γ) :
    U.length + (I.toList.map Segment.length).sum = Δ.length + Γ.length := by
  obtain ⟨ρ, a, b, c, d, hΔ, hΓ, ⟨hac, hcb, hbd⟩, hU, hI⟩ :=
    hs.coordinates hfree hp
  have hΔlen := hΔ.2
  have hΓlen := hΓ.2
  have hUlen := hU.2
  cases I with
  | none =>
    have he : Δ.support ∩ Γ.support = ∅ := hs.2
    have hbc : b < c := by
      by_contra hn
      have hm : ρ.twist (c : ℝ) ∈ Δ.support ∩ Γ.support :=
        ⟨(hΔ.twist_mem_support_iff hfree).mpr ⟨by omega, by omega⟩,
          (hΓ.twist_mem_support_iff hfree).mpr ⟨le_refl _, hΓ.lower_le_upper⟩⟩
      rw [he] at hm
      exact hm
    simp only [Option.toList_none, List.map_nil, List.sum_nil, Nat.add_zero]
    omega
  | some J =>
    have hJlen := (hI J rfl).2
    simp only [Option.toList_some, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.add_zero]
    omega

/-- Every actual replacement preserves total general-linear rank. -/
theorem IsUnionIntersectionReplacement.degree_sum
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {Δ Γ U : Segment.{uV, uF} T} {I : Option (Segment.{uV, uF} T)}
    (hs : IsUnionIntersectionReplacement Δ Γ U I) (hp : Δ.Precedes Γ) :
    U.degree + (I.toList.map Segment.degree).sum = Δ.degree + Γ.degree := by
  have hlen := hs.length_sum hfree hp
  obtain ⟨ρ, a, b, c, d, hΔ, hΓ, _, hU, hI⟩ := hs.coordinates hfree hp
  cases I with
  | none =>
    simp only [Option.toList_none, List.map_nil, List.sum_nil, Nat.add_zero] at hlen ⊢
    simp only [degree, hΔ.rank_eq, hΓ.rank_eq, hU.rank_eq, hlen, Nat.add_mul]
  | some J =>
    have hrJ := (hI J rfl).rank_eq
    simp only [Option.toList_some, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.add_zero] at hlen ⊢
    simp only [degree, hΔ.rank_eq, hΓ.rank_eq, hU.rank_eq, hrJ, ← Nat.add_mul, hlen]

/-- Choose actual union and optional intersection segments for a preceding pair. -/
def unionIntersectionPair
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    (Δ Γ : Segment.{uV, uF} T) (hp : Δ.Precedes Γ) :
    Segment.{uV, uF} T × Option (Segment.{uV, uF} T) :=
  let hex := exists_unionIntersectionReplacement hfree hp
  (Classical.choose hex, Classical.choose (Classical.choose_spec hex))

theorem unionIntersectionPair_spec
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    (Δ Γ : Segment.{uV, uF} T) (hp : Δ.Precedes Γ) :
    IsUnionIntersectionReplacement Δ Γ
      (unionIntersectionPair hfree Δ Γ hp).1 (unionIntersectionPair hfree Δ Γ hp).2 :=
  Classical.choose_spec (Classical.choose_spec (exists_unionIntersectionReplacement hfree hp))

/-- A union/intersection replacement preserves the degree of the complete
occurrence list, with every outside segment retained. -/
theorem IsUnionIntersectionReplacement.degree_sum_append
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {Δ Γ U : Segment.{uV, uF} T} {I : Option (Segment.{uV, uF} T)}
    (hs : IsUnionIntersectionReplacement Δ Γ U I) (hp : Δ.Precedes Γ)
    (l r : List (Segment.{uV, uF} T)) :
    ((l ++ [U] ++ I.toList ++ r).map Segment.degree).sum =
      ((l ++ [Δ, Γ] ++ r).map Segment.degree).sum := by
  have hsum := hs.degree_sum hfree hp
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]
  omega

end Segment

end Langlands.PadicField.TopologicalData
