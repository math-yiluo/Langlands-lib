import Langlands.Representation.Classification.SegmentUnionIntersection
import Langlands.Representation.Classification.SegmentInitialTruncation

/-! Truncation `Δ ↦ Δ⁻` of a preceding pair of overlapping segments, with its
union and intersection. The truncations are the published `Segment.dropLastNonempty`
and `Segment.dropLast`. -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace Segment

theorem HasIntegralCoordinates.dropLastNonempty {Δ : Segment.{uV, uF} T}
    {ρ : CuspidalDatum.{uV, uF} T} {a b : ℤ}
    (hΔ : Δ.HasIntegralCoordinates ρ a b) (h : 1 < Δ.length) :
    (Δ.dropLastNonempty h).HasIntegralCoordinates ρ a (b - 1) := by
  refine ⟨hΔ.1, ?_⟩
  have := hΔ.2
  change b - 1 = a + ((Δ.length - 1 : ℕ) : ℤ) - 1
  omega

theorem isJuxtaposed_comm (Δ Γ : Segment.{uV, uF} T) :
    Δ.IsJuxtaposed Γ ↔ Γ.IsJuxtaposed Δ :=
  ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩

theorem IsUnionIntersectionReplacement.symm {Δ Γ U : Segment.{uV, uF} T}
    {I : Option (Segment.{uV, uF} T)} (h : IsUnionIntersectionReplacement Δ Γ U I) :
    IsUnionIntersectionReplacement Γ Δ U I := by
  refine ⟨h.1.trans (Set.union_comm _ _), ?_⟩
  cases I with
  | none => exact (Set.inter_comm _ _).trans h.2
  | some J => exact h.2.trans (Set.inter_comm _ _)

/-- Under integral twist freeness the union and the optional intersection are
determined by the pair. -/
theorem IsUnionIntersectionReplacement.unique
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {Δ Γ U₁ U₂ : Segment.{uV, uF} T} {I₁ I₂ : Option (Segment.{uV, uF} T)}
    (h₁ : IsUnionIntersectionReplacement Δ Γ U₁ I₁)
    (h₂ : IsUnionIntersectionReplacement Δ Γ U₂ I₂) :
    U₁ = U₂ ∧ I₁ = I₂ := by
  refine ⟨eq_of_support_eq hfree (h₁.1.trans h₂.1.symm), ?_⟩
  have key : ∀ J : Segment.{uV, uF} T, J.support = Δ.support ∩ Γ.support →
      Δ.support ∩ Γ.support ≠ ∅ := by
    intro J hJ h
    have hm := J.base_mem_support
    rw [hJ, h] at hm
    exact hm
  cases I₁ with
  | none =>
    cases I₂ with
    | none => rfl
    | some J => exact absurd h₁.2 (key J h₂.2)
  | some J =>
    cases I₂ with
    | none => exact absurd h₂.2 (key J h₁.2)
    | some J' => exact congrArg some (eq_of_support_eq hfree (h₁.2.trans h₂.2.symm))

/-- Let `A` precede `B` without being juxtaposed with it. Then both have length at
least two, the union `U` has length at least two and the intersection `J` is
nonempty; `A⁻` precedes `B⁻`, whose union is `U⁻` and whose intersection is
`J⁻` (empty when `J` is a singleton). All four segments have the rank of `A`, and
`J ⊆ U`. -/
theorem Precedes.truncation
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {A B : Segment.{uV, uF} T} (hp : A.Precedes B) (hj : ¬ A.IsJuxtaposed B) :
    ∃ (hA : 1 < A.length) (hB : 1 < B.length) (U J : Segment.{uV, uF} T)
      (hU : 1 < U.length),
      IsUnionIntersectionReplacement B A U (some J) ∧
        (A.dropLastNonempty hA).Precedes (B.dropLastNonempty hB) ∧
        IsUnionIntersectionReplacement (B.dropLastNonempty hB) (A.dropLastNonempty hA)
          (U.dropLastNonempty hU) J.dropLast ∧
        B.rank = A.rank ∧ U.rank = A.rank ∧ J.rank = A.rank ∧ J.support ⊆ U.support := by
  have hAc := A.hasIntegralCoordinates_self
  obtain ⟨c, e, hBc⟩ := hAc.of_precedes_right hp
  obtain ⟨hac, hcb, hbe⟩ := hAc.intervalPrecedes_of_precedes hfree hBc hp
  have hov : c ≤ (A.length : ℤ) - 1 := by
    by_contra hlt
    apply hj
    refine ⟨hp.1, ?_⟩
    rw [Set.disjoint_iff_inter_eq_empty]
    exact hAc.support_inter_eq_empty hfree hBc (by omega)
  have hA : 1 < A.length := by omega
  have hB : 1 < B.length := by have := hBc.2; omega
  have hUc := ofIntegralInterval_hasIntegralCoordinates A.base 0 e (by omega)
  have hJc := ofIntegralInterval_hasIntegralCoordinates A.base c ((A.length : ℤ) - 1) hov
  set U := ofIntegralInterval A.base 0 e (by omega)
  set J := ofIntegralInterval A.base c ((A.length : ℤ) - 1) hov
  have hU : 1 < U.length := by have := hUc.2; omega
  have hA' := hAc.dropLastNonempty hA
  have hB' := hBc.dropLastNonempty hB
  have hU' := hUc.dropLastNonempty hU
  have hUsupp : (U.dropLastNonempty hU).support =
      (A.dropLastNonempty hA).support ∪ (B.dropLastNonempty hB).support :=
    ((hU'.support_eq_iff hfree
      (ofIntegralInterval_hasIntegralCoordinates A.base 0 (e - 1) (by omega))).2
        ⟨rfl, rfl⟩).trans (hA'.support_union_eq hB' (by omega) (by omega) (by omega))
  refine ⟨hA, hB, U, J, hU, ?_, ?_, ?_, hBc.rank_eq, hUc.rank_eq, hJc.rank_eq, ?_⟩
  · exact IsUnionIntersectionReplacement.symm
      ⟨hAc.support_union_eq hBc (by omega) hcb (by omega),
        hAc.support_inter_eq hfree hBc (by omega) (by omega) hov⟩
  · exact hA'.precedes_of_intervalPrecedes hfree hB' ⟨hac, by omega, by omega⟩
  · by_cases hJ : 1 < J.length
    · rw [J.dropLast_of_one_lt hJ]
      refine IsUnionIntersectionReplacement.symm ⟨hUsupp, ?_⟩
      have hJ' := hJc.dropLastNonempty hJ
      change (J.dropLastNonempty hJ).support =
        (A.dropLastNonempty hA).support ∩ (B.dropLastNonempty hB).support
      have hle : c ≤ (A.length : ℤ) - 1 - 1 := by have := hJc.2; omega
      exact ((hJ'.support_eq_iff hfree
        (ofIntegralInterval_hasIntegralCoordinates A.base c ((A.length : ℤ) - 1 - 1)
          hle)).2 ⟨rfl, rfl⟩).trans
        (hA'.support_inter_eq hfree hB' (by omega) (by omega) hle)
    · rw [J.dropLast_of_length_eq_one (by have := J.length_pos; omega)]
      refine IsUnionIntersectionReplacement.symm ⟨hUsupp, ?_⟩
      change (A.dropLastNonempty hA).support ∩ (B.dropLastNonempty hB).support = ∅
      have := hJc.2
      exact hA'.support_inter_eq_empty hfree hB' (by omega)
  · exact (hJc.support_subset_iff hfree hUc).2 ⟨by omega, by omega⟩

end Segment

end Langlands.PadicField.TopologicalData
