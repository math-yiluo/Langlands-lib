import Langlands.Representation.Classification.SegmentTruncationObstructionStatement
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
import Langlands.Representation.Classification.SegmentIntervalLinkage

/-!
# Proof of the finite segment-truncation obstruction

The combinatorial lemma of Zelevinsky 1980, §9.8, printed p.200. Actual segments
meeting one integral twist line receive integer coordinates there; integral twist
freeness makes these coordinates faithful, so the finite endpoint choice and the
two nonlinkage containment steps become integer inequalities.
-/

noncomputable section

namespace Langlands

universe uF uV

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace Segment

/-- A segment with a member on the integral twist line through `σ` has integral
coordinates on that line. -/
theorem exists_hasIntegralCoordinates_of_twist_mem
    {Δ : Segment.{uV, uF} T} {σ : CuspidalDatum.{uV, uF} T} {t : ℤ}
    (h : σ.twist (t : ℝ) ∈ Δ.support) :
    ∃ a : ℤ, Δ.HasIntegralCoordinates σ a (a + Δ.length - 1) := by
  obtain ⟨i, -, hi⟩ := h
  refine ⟨t - i, ?_, rfl⟩
  have he := congrArg (fun τ : CuspidalDatum.{uV, uF} T => τ.twist (-(i : ℝ))) hi
  simp only [member, CuspidalDatum.twist_twist, neg_add_cancel,
    CuspidalDatum.twist_zero] at he
  rw [he]
  congr 1
  push_cast
  ring

/-- A segment containing `σ` has integral coordinates on the twist line through `σ`. -/
theorem exists_hasIntegralCoordinates_of_mem
    {Δ : Segment.{uV, uF} T} {σ : CuspidalDatum.{uV, uF} T} (h : σ ∈ Δ.support) :
    ∃ a : ℤ, Δ.HasIntegralCoordinates σ a (a + Δ.length - 1) :=
  exists_hasIntegralCoordinates_of_twist_mem (t := 0) (by simpa using h)

/-- The end of a segment with integral coordinates `[a, b]` is `ν^b ρ`. -/
theorem HasIntegralCoordinates.last_eq
    {Δ : Segment.{uV, uF} T} {ρ : CuspidalDatum.{uV, uF} T} {a b : ℤ}
    (h : Δ.HasIntegralCoordinates ρ a b) : Δ.last = ρ.twist (b : ℝ) := by
  have hlen := Δ.length_pos
  have hb : a + ((Δ.length - 1 : ℕ) : ℤ) = b := by
    have := h.2
    omega
  rw [last, h.member_eq, hb]

/-- The integral exponents placing the line through `σ` in a segment form a
finite set. Twist freeness excludes a periodic line. -/
theorem finite_setOf_twist_mem_support
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    (σ : CuspidalDatum.{uV, uF} T) (Δ : Segment.{uV, uF} T) :
    {t : ℤ | σ.twist (t : ℝ) ∈ Δ.support}.Finite := by
  by_cases h : ∃ t : ℤ, σ.twist (t : ℝ) ∈ Δ.support
  · obtain ⟨t, ht⟩ := h
    obtain ⟨a, ha⟩ := exists_hasIntegralCoordinates_of_twist_mem ht
    refine (Set.finite_Icc a (a + Δ.length - 1)).subset fun k hk => ?_
    exact Set.mem_Icc.mpr ((ha.twist_mem_support_iff hfree).mp hk)
  · exact Set.finite_empty.subset fun k hk => h ⟨k, hk⟩

/-- The same finiteness for a possibly empty segment. -/
theorem finite_setOf_twist_mem_optionalSupport
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    (σ : CuspidalDatum.{uV, uF} T) (A : Option (Segment.{uV, uF} T)) :
    {t : ℤ | σ.twist (t : ℝ) ∈ optionalSupport A}.Finite := by
  cases A with
  | none => simp [optionalSupport]
  | some E => exact finite_setOf_twist_mem_support hfree σ E

/-- The finite endpoint choice: a nonempty finite union of possibly empty actual
segment supports contains some `ρ` whose twist `νρ` lies outside the union. -/
theorem exists_mem_iUnion_optionalSupport_twist_one_not_mem
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {ι : Type*} [Finite ι] (A : ι → Option (Segment.{uV, uF} T))
    (hne : (⋃ i, optionalSupport (A i)).Nonempty) :
    ∃ ρ ∈ ⋃ i, optionalSupport (A i), ρ.twist 1 ∉ ⋃ i, optionalSupport (A i) := by
  obtain ⟨σ, hσ⟩ := hne
  have hset : {t : ℤ | σ.twist (t : ℝ) ∈ ⋃ i, optionalSupport (A i)} =
      ⋃ i, {t : ℤ | σ.twist (t : ℝ) ∈ optionalSupport (A i)} := by
    ext t
    simp
  have hfin : {t : ℤ | σ.twist (t : ℝ) ∈ ⋃ i, optionalSupport (A i)}.Finite := by
    rw [hset]
    exact Set.finite_iUnion fun i => finite_setOf_twist_mem_optionalSupport hfree σ (A i)
  obtain ⟨M, hM⟩ := hfin.exists_maximal ⟨0, by simpa using hσ⟩
  refine ⟨σ.twist (M : ℝ), hM.1, fun hmem => ?_⟩
  have h1 : (M + 1 : ℤ) ∈ {t : ℤ | σ.twist (t : ℝ) ∈ ⋃ i, optionalSupport (A i)} := by
    rw [CuspidalDatum.twist_twist] at hmem
    show σ.twist ((M + 1 : ℤ) : ℝ) ∈ ⋃ i, optionalSupport (A i)
    convert hmem using 2
    push_cast
    ring
  have := hM.2 h1 (by omega)
  omega

/-- A point of a terminal truncation exhibits it as an actual segment. -/
theorem IsTerminalTruncation.exists_of_mem
    {A : Option (Segment.{uV, uF} T)} {Δ : Segment.{uV, uF} T}
    (hA : IsTerminalTruncation A Δ) {σ : CuspidalDatum.{uV, uF} T}
    (hσ : σ ∈ optionalSupport A) :
    ∃ E : Segment.{uV, uF} T, optionalSupport A = E.support ∧
      E.support ⊆ Δ.support ∧ Δ.last ∈ E.support := by
  cases A with
  | none => simp [optionalSupport] at hσ
  | some E => exact ⟨E, rfl, hA⟩

/-- A point of an initial truncation exhibits it as an actual segment. -/
theorem IsInitialTruncation.exists_of_mem
    {B : Option (Segment.{uV, uF} T)} {Δ : Segment.{uV, uF} T}
    (hB : IsInitialTruncation B Δ) {σ : CuspidalDatum.{uV, uF} T}
    (hσ : σ ∈ optionalSupport B) :
    ∃ E : Segment.{uV, uF} T, optionalSupport B = E.support ∧
      E.support ⊆ Δ.support ∧ Δ.base ∈ E.support := by
  cases B with
  | none => simp [optionalSupport] at hσ
  | some E => exact ⟨E, rfl, hB⟩

/-- Two overlapping or juxtaposed segments on one free twist line are linked or
nested. -/
theorem HasIntegralCoordinates.support_subset_or_subset_of_not_isLinked
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {Δ Γ : Segment.{uV, uF} T} {ρ : CuspidalDatum.{uV, uF} T} {a b c d : ℤ}
    (hΔ : Δ.HasIntegralCoordinates ρ a b) (hΓ : Γ.HasIntegralCoordinates ρ c d)
    (hcb : c ≤ b + 1) (had : a ≤ d + 1) (hnl : ¬ Δ.IsLinked Γ) :
    Δ.support ⊆ Γ.support ∨ Γ.support ⊆ Δ.support := by
  by_cases h₁ : IntervalPrecedes a b c d
  · exact absurd (hΔ.precedes_of_intervalPrecedes hfree hΓ h₁).isLinked hnl
  by_cases h₂ : IntervalPrecedes c d a b
  · exact absurd (hΓ.precedes_of_intervalPrecedes hfree hΔ h₂).isLinked.symm hnl
  unfold IntervalPrecedes at h₁ h₂
  rw [hΔ.support_subset_iff hfree hΓ, hΓ.support_subset_iff hfree hΔ]
  omega

end Segment

end PadicField.TopologicalData

namespace Classification

open PadicField.TopologicalData

/-- Zelevinsky 1980, §9.8, printed p.200: if the union of the initial truncations
is the nonempty one-step twist of the union of the terminal truncations, two of the
original segments are linked. -/
theorem segmentTruncationObstruction
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    SegmentTruncationObstruction.{uF, uV} F T := by
  have hfree := cuspidalIntegralTwistFreeness.{uF, uV} F T
  intro r Δ A B hA hB hU hne
  by_contra hlink
  push Not at hlink
  have memA : ∀ (l : Fin r) {σ : CuspidalDatum.{uV, uF} T},
      σ ∈ Segment.optionalSupport (A l) → σ ∈ ⋃ i, Segment.optionalSupport (A i) :=
    fun l _ h => Set.mem_iUnion.mpr ⟨l, h⟩
  have hneA : (⋃ i, Segment.optionalSupport (A i)).Nonempty := by
    obtain ⟨τ, hτ⟩ := hne
    rw [hU] at hτ
    obtain ⟨ρ, hρ, -⟩ := hτ
    exact ⟨ρ, hρ⟩
  -- The endpoint: `ρ` in some terminal truncation, `νρ` in none.
  obtain ⟨ρ, hρ, hνρ⟩ :=
    Segment.exists_mem_iUnion_optionalSupport_twist_one_not_mem hfree A hneA
  obtain ⟨i, hρi⟩ := Set.mem_iUnion.mp hρ
  obtain ⟨Ei, hEiA, hEiΔ, hlasti⟩ := (hA i).exists_of_mem hρi
  rw [hEiA] at hρi
  obtain ⟨ai, hΔi⟩ := Segment.exists_hasIntegralCoordinates_of_mem (hEiΔ hρi)
  obtain ⟨ci, hEi⟩ := Segment.exists_hasIntegralCoordinates_of_mem hρi
  have hρ0 : ∀ {S : Set (CuspidalDatum.{uV, uF} T)}, ρ ∈ S → ρ.twist ((0 : ℤ) : ℝ) ∈ S :=
    fun h => by simpa using h
  have h0i := (hΔi.twist_mem_support_iff hfree).mp (hρ0 (hEiΔ hρi))
  have h0Ei := (hEi.twist_mem_support_iff hfree).mp (hρ0 hρi)
  rw [hΔi.last_eq] at hlasti
  have hlastEi := (hEi.twist_mem_support_iff hfree).mp hlasti
  -- `ρ` is the end of its terminal truncation, hence of `Δ i`.
  have hbi : ai + ((Δ i).length : ℤ) - 1 = 0 := by
    by_contra hbi
    apply hνρ
    apply memA i
    rw [hEiA]
    have := (hEi.twist_mem_support_iff hfree (k := 1)).mpr ⟨by omega, by omega⟩
    simpa using this
  -- `νρ` lies in an initial truncation of `Δ j`.
  have hνB : ρ.twist 1 ∈ ⋃ j, Segment.optionalSupport (B j) := by
    rw [hU]
    exact ⟨ρ, hρ, rfl⟩
  obtain ⟨j, hνj⟩ := Set.mem_iUnion.mp hνB
  obtain ⟨Ej, hEjB, hEjΔ, hbasej⟩ := (hB j).exists_of_mem hνj
  rw [hEjB] at hνj
  have hνΔj : ρ.twist ((1 : ℤ) : ℝ) ∈ (Δ j).support := by
    simpa using hEjΔ hνj
  obtain ⟨aj, hΔj⟩ := Segment.exists_hasIntegralCoordinates_of_twist_mem hνΔj
  have h1j := (hΔj.twist_mem_support_iff hfree).mp hνΔj
  -- First containment: nonlinkage forces `Δ i ⊆ Δ j`.
  have hij : (Δ i).support ⊆ (Δ j).support := by
    rcases hΔi.support_subset_or_subset_of_not_isLinked hfree hΔj (by omega) (by omega)
        (hlink i j) with h | h
    · exact h
    · have := (hΔj.support_subset_iff hfree hΔi).mp h
      omega
  have hij' := (hΔi.support_subset_iff hfree hΔj).mp hij
  -- The beginning `ρ₁ = ν^{aj} ρ` of `Δ j` gives `ν⁻¹ρ₁` in a terminal truncation.
  have hbaseB : (Δ j).base ∈ ⋃ l, Segment.optionalSupport (B l) :=
    Set.mem_iUnion.mpr ⟨j, by rw [hEjB]; exact hbasej⟩
  rw [hU] at hbaseB
  obtain ⟨τ, hτ, hτeq⟩ := hbaseB
  have hτρ : τ = ρ.twist ((aj - 1 : ℤ) : ℝ) := by
    have h := congrArg (fun σ : CuspidalDatum.{uV, uF} T => σ.twist (-1 : ℝ)) hτeq
    simp only [CuspidalDatum.twist_twist, hΔj.1, neg_add_cancel,
      CuspidalDatum.twist_zero] at h
    rw [h]
    congr 1
    push_cast
    ring
  obtain ⟨k, hτk⟩ := Set.mem_iUnion.mp hτ
  obtain ⟨Ek, hEkA, hEkΔ, hlastk⟩ := (hA k).exists_of_mem hτk
  rw [hEkA, hτρ] at hτk
  obtain ⟨ak, hΔk⟩ := Segment.exists_hasIntegralCoordinates_of_twist_mem (hEkΔ hτk)
  obtain ⟨ck, hEk⟩ := Segment.exists_hasIntegralCoordinates_of_twist_mem hτk
  have hτΔk := (hΔk.twist_mem_support_iff hfree).mp (hEkΔ hτk)
  have hτEk := (hEk.twist_mem_support_iff hfree).mp hτk
  rw [hΔk.last_eq] at hlastk
  have hlastEk := (hEk.twist_mem_support_iff hfree).mp hlastk
  -- Second containment: nonlinkage forces `Δ j ⊆ Δ k`.
  have hjk : (Δ j).support ⊆ (Δ k).support := by
    rcases hΔj.support_subset_or_subset_of_not_isLinked hfree hΔk (by omega) (by omega)
        (hlink j k) with h | h
    · exact h
    · have := (hΔk.support_subset_iff hfree hΔj).mp h
      omega
  have hjk' := (hΔj.support_subset_iff hfree hΔk).mp hjk
  -- Hence the terminal truncation of `Δ k` contains `νρ`.
  apply hνρ
  apply memA k
  rw [hEkA]
  have := (hEk.twist_mem_support_iff hfree (k := 1)).mpr ⟨by omega, by omega⟩
  simpa using this

end Classification

end Langlands
