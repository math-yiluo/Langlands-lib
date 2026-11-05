import Langlands.Representation.Classification.SegmentUnionIntersection
import Langlands.Representation.Classification.SegmentTruncationObstructionProof

/-! An actual terminal segment distinguishing a linked pair from its
union/intersection replacement. No representation derivative is identified. -/

noncomputable section

namespace Langlands.PadicField.TopologicalData.Segment

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- A terminal truncation of an optional segment; an absent source forces an
absent truncation. -/
def IsTerminalTruncationOfOptional
    (B I : Option (Segment.{uV, uF} T)) : Prop :=
  match I with
  | none => B = none
  | some J => IsTerminalTruncation B J

/-- The concrete cut and support obstruction used for a preceding linked pair.
This is segment data only, without an occurrence assertion. -/
structure LinkedTerminalWitness
    (Δ Γ U : Segment.{uV, uF} T) (I : Option (Segment.{uV, uF} T)) where
  segment : Segment.{uV, uF} T
  cut : ℕ
  cut_lt : cut < Δ.length
  base_eq : segment.base = Δ.base.twist (cut : ℝ)
  length_add_cut : segment.length + cut = Δ.length
  base_eq_right : segment.base = Γ.base.twist (-1)
  terminal : IsTerminalTruncation (some segment) Δ
  support_eq_inter : segment.support = Δ.support ∩ (Γ.twist (-1)).support
  not_replacement : ∀ A B : Option (Segment.{uV, uF} T),
    IsTerminalTruncation A U → IsTerminalTruncationOfOptional B I →
    segment.support ≠ optionalSupport A ∪ optionalSupport B

/-- For `Δ=[a,b]` preceding `Γ=[c,d]`, choose the nonempty segment `[c-1,b]`
and its cut in `Δ`. Its support cannot be a union of terminal truncations of
the replacement union and optional intersection. -/
def linkedTerminalWitness
    (hfree : Langlands.Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {Δ Γ U : Segment.{uV, uF} T} {I : Option (Segment.{uV, uF} T)}
    (hp : Δ.Precedes Γ) (hs : IsUnionIntersectionReplacement Δ Γ U I) :
    LinkedTerminalWitness Δ Γ U I := by
  apply Classical.choice
  obtain ⟨ρ, a, b, c, d, hΔ, hΓ, ⟨hac, hcb, hbd⟩, hU, hI⟩ :=
    hs.coordinates hfree hp
  let E := ofIntegralInterval ρ (c - 1) b (by omega)
  have hE : E.HasIntegralCoordinates ρ (c - 1) b :=
    ofIntegralInterval_hasIntegralCoordinates _ _ _ _
  have hΓ' : (Γ.twist (-1)).HasIntegralCoordinates ρ (c - 1) (d - 1) := by
    constructor
    · change Γ.base.twist (-1) = ρ.twist ((c - 1 : ℤ) : ℝ)
      rw [hΓ.1, CuspidalDatum.twist_twist]
      congr 1
      push_cast
      ring
    · change d - 1 = c - 1 + (Γ.length : ℤ) - 1
      have := hΓ.2
      omega
  have hbase : E.base = Γ.base.twist (-1) := hE.1.trans hΓ'.1.symm
  have hbase_not : E.base ∉ Γ.support := by
    rw [hE.1, hΓ.twist_mem_support_iff hfree]
    omega
  have hlast_not : U.last ∉ E.support := by
    rw [hU.last_eq, hE.twist_mem_support_iff hfree]
    omega
  have hcut : ((c - 1 - a).toNat : ℤ) = c - 1 - a :=
    Int.toNat_of_nonneg (by omega)
  refine ⟨{
    segment := E
    cut := (c - 1 - a).toNat
    cut_lt := by have := hΔ.2; omega
    base_eq := ?_
    length_add_cut := by have := hΔ.2; have := hE.2; omega
    base_eq_right := hbase
    terminal := ?_
    support_eq_inter := ?_
    not_replacement := ?_
  }⟩
  · rw [hE.1, hΔ.1, CuspidalDatum.twist_twist]
    congr 1
    have he : (a : ℝ) + ((c - 1 - a).toNat : ℝ) = ((c - 1 : ℤ) : ℝ) := by
      exact_mod_cast (show a + ((c - 1 - a).toNat : ℤ) = c - 1 by omega)
    simpa only [add_comm] using he.symm
  · exact ⟨(hE.support_subset_iff hfree hΔ).mpr ⟨by omega, le_refl _⟩,
      by rw [hΔ.last_eq]; exact (hE.twist_mem_support_iff hfree).mpr ⟨by omega, le_refl _⟩⟩
  · exact hΔ.support_inter_eq hfree hΓ' (by omega) (by omega) (by omega)
  · intro A B hA hB heq
    cases A with
    | some S =>
      have hm : U.last ∈ optionalSupport (some S) ∪ optionalSupport B :=
        Or.inl hA.2
      exact hlast_not (heq.symm ▸ hm)
    | none =>
      have hm : E.base ∈ optionalSupport B := by
        have := heq ▸ E.base_mem_support
        simpa only [optionalSupport, Set.empty_union] using this
      cases I with
      | none =>
        change B = none at hB
        rw [hB] at hm
        exact hm
      | some J =>
        have hJ : J.support = Δ.support ∩ Γ.support := hs.2
        cases B with
        | none => exact hm
        | some S => exact hbase_not (hJ ▸ hB.1 hm).2

end Langlands.PadicField.TopologicalData.Segment
