import Langlands.Representation.Classification.UnlinkedCuspidalContentInjectivityStatement
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
import Langlands.Representation.Classification.SegmentIntervalLinkage

/-!
# Reconstruction of an unlinked multisegment from cuspidal content

An unlinked multisegment is recovered from its cuspidal content by repeatedly removing
the longest segment that begins at a left end of the content.
-/

noncomputable section

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace Segment

/-- A segment is determined by its beginning and its length. -/
theorem ext_of_base_length {Δ Γ : Segment.{uV, uF} T} (hb : Δ.base = Γ.base)
    (hl : Δ.length = Γ.length) : Δ = Γ := by
  cases Δ
  cases Γ
  simp_all

/-- A segment whose support lies in `S` and contains a left end `ρ` of `S`, meaning
that `ν^(-1) ρ ∉ S`, begins at `ρ`. -/
theorem base_eq_of_left_end {S : Set (CuspidalDatum.{uV, uF} T)} {Δ : Segment.{uV, uF} T}
    {ρ : CuspidalDatum.{uV, uF} T} (hsub : Δ.support ⊆ S) (hρ : ρ ∈ Δ.support)
    (hleft : ρ.twist (-1 : ℝ) ∉ S) : Δ.base = ρ := by
  obtain ⟨i, hi, rfl⟩ := hρ
  cases i with
  | zero => simp
  | succ i =>
    exfalso
    apply hleft
    have he : (Δ.member (i + 1)).twist (-1 : ℝ) = Δ.member i := by
      simp only [member, CuspidalDatum.twist_twist]
      congr 1
      push_cast
      ring
    rw [he]
    exact hsub (Δ.member_mem_support (by omega))

end Segment

namespace Multisegment

/-- A datum occurs in the cuspidal content exactly when it lies in the support of some
segment of the multisegment. -/
theorem mem_cuspidalContent_iff (a : Multisegment.{uV, uF} T) (σ : CuspidalDatum.{uV, uF} T) :
    σ ∈ a.cuspidalContent ↔ ∃ Δ ∈ a, σ ∈ Δ.support := by
  induction a using Multiset.induction_on with
  | empty => simp
  | cons Δ a ih =>
    rw [cuspidalContent_cons, Multiset.mem_add, Segment.mem_cuspidalContent, ih]
    simp only [Multiset.mem_cons, exists_eq_or_imp]

theorem support_subset_cuspidalContent {a : Multisegment.{uV, uF} T} {Δ : Segment.{uV, uF} T}
    (h : Δ ∈ a) : Δ.support ⊆ {σ | σ ∈ a.cuspidalContent} := fun σ hσ =>
  (mem_cuspidalContent_iff a σ).mpr ⟨Δ, h, hσ⟩

/-- Only the empty multisegment has empty cuspidal content. -/
theorem cuspidalContent_eq_zero_iff (a : Multisegment.{uV, uF} T) :
    a.cuspidalContent = 0 ↔ a = 0 := by
  constructor
  · intro h
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro Δ hΔ
    have hm := (mem_cuspidalContent_iff a Δ.base).mpr ⟨Δ, hΔ, Δ.base_mem_support⟩
    rw [h] at hm
    exact Multiset.notMem_zero _ hm
  · rintro rfl
    simp

/-- Submultisets of unlinked multisegments are unlinked. -/
theorem IsUnlinked.of_le {a b : Multisegment.{uV, uF} T} (hb : b.IsUnlinked) (h : a ≤ b) :
    a.IsUnlinked :=
  fun Δ₁ h₁ Δ₂ h₂ => hb Δ₁ (Multiset.mem_of_le h h₁) Δ₂ (Multiset.mem_of_le h h₂)

end Multisegment

namespace UnlinkedReconstruction

/-- Under integral twist freeness, every finite multiset of cuspidal data containing `σ`
has a left end: an element `ρ` with `ν^(-1) ρ` outside it. -/
theorem exists_left_end
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    (S : Multiset (CuspidalDatum.{uV, uF} T)) {σ : CuspidalDatum.{uV, uF} T} (hσ : σ ∈ S) :
    ∃ ρ ∈ S, ρ.twist (-1 : ℝ) ∉ S := by
  classical
  by_contra hcon
  push Not at hcon
  have hall : ∀ n : ℕ, σ.twist (-(n : ℝ)) ∈ S := by
    intro n
    induction n with
    | zero => simpa using hσ
    | succ n ih =>
      have hn := hcon _ ih
      rw [CuspidalDatum.twist_twist] at hn
      have he : (-((n + 1 : ℕ) : ℝ)) = -1 + -(n : ℝ) := by
        push_cast
        ring
      rw [he]
      exact hn
  have hinj : Function.Injective (fun n : ℕ => σ.twist (-(n : ℝ))) := by
    intro m n h
    have h' : (fun k : ℤ => σ.twist (k : ℝ)) (-(m : ℤ)) =
        (fun k : ℤ => σ.twist (k : ℝ)) (-(n : ℤ)) := by
      simpa only [Int.cast_neg, Int.cast_natCast] using h
    have := σ.integralTwist_injective hfree h'
    omega
  have hinf := Set.infinite_of_injective_forall_mem (s := (S.toFinset : Set _)) hinj
    (fun n => by simpa using hall n)
  exact hinf S.toFinset.finite_toSet

/-- At a left end `ρ` of the content of `a`, some segment of `a` begins at `ρ`, and a
longest such segment exists. -/
theorem exists_longest_at_left_end {a : Multisegment.{uV, uF} T}
    {ρ : CuspidalDatum.{uV, uF} T} (hρ : ρ ∈ a.cuspidalContent)
    (hleft : ρ.twist (-1 : ℝ) ∉ a.cuspidalContent) :
    ∃ Γ ∈ a, Γ.base = ρ ∧ ∀ Λ ∈ a, Λ.base = ρ → Λ.length ≤ Γ.length := by
  classical
  obtain ⟨Δ, hΔ, hρΔ⟩ := (Multisegment.mem_cuspidalContent_iff a ρ).mp hρ
  have hbase : Δ.base = ρ :=
    Segment.base_eq_of_left_end (Multisegment.support_subset_cuspidalContent hΔ) hρΔ hleft
  have hne : a.filter (fun Λ => Λ.base = ρ) ≠ 0 := by
    intro h0
    have hm : Δ ∈ a.filter (fun Λ => Λ.base = ρ) := Multiset.mem_filter.mpr ⟨hΔ, hbase⟩
    rw [h0] at hm
    exact Multiset.notMem_zero _ hm
  obtain ⟨Γ, hΓ, hmax⟩ := Multiset.exists_max_image Segment.length hne
  obtain ⟨hΓa, hΓρ⟩ := Multiset.mem_filter.mp hΓ
  exact ⟨Γ, hΓa, hΓρ, fun Λ hΛ hΛρ => hmax Λ (Multiset.mem_filter.mpr ⟨hΛ, hΛρ⟩)⟩

/-- In an unlinked multisegment, a longest segment `Γ` beginning at a left end of the
content also ends at a right end: `ν^(length Γ)` of its beginning is not in the content. -/
theorem twist_length_notMem
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {a : Multisegment.{uV, uF} T} (ha : a.IsUnlinked) {Γ : Segment.{uV, uF} T} (hΓ : Γ ∈ a)
    (hleft : Γ.base.twist (-1 : ℝ) ∉ a.cuspidalContent)
    (hmax : ∀ Λ ∈ a, Λ.base = Γ.base → Λ.length ≤ Γ.length) :
    Γ.base.twist (Γ.length : ℝ) ∉ a.cuspidalContent := by
  intro hmem
  obtain ⟨Λ, hΛ, i, hi, hΛi⟩ := (Multisegment.mem_cuspidalContent_iff a _).mp hmem
  have hΓc := Γ.hasIntegralCoordinates_self
  have hΓpos := Γ.length_pos
  have hΛc : Λ.HasIntegralCoordinates Γ.base ((Γ.length : ℤ) - i)
      ((Γ.length : ℤ) - i + Λ.length - 1) := by
    refine ⟨?_, rfl⟩
    have he := congrArg (fun σ : CuspidalDatum.{uV, uF} T => σ.twist (-(i : ℝ))) hΛi
    simp only [Segment.member, CuspidalDatum.twist_twist, neg_add_cancel,
      CuspidalDatum.twist_zero] at he
    rw [he]
    congr 1
    push_cast
    ring
  rcases lt_trichotomy ((Γ.length : ℤ) - i) 0 with hs | hs | hs
  · apply hleft
    refine (Multisegment.mem_cuspidalContent_iff a _).mpr ⟨Λ, hΛ, ?_⟩
    have hm := (hΛc.twist_mem_support_iff hfree (k := -1)).mpr ⟨by omega, by omega⟩
    simpa using hm
  · have hb : Λ.base = Γ.base := by
      rw [hΛc.1, hs]
      simp
    have := hmax Λ hΛ hb
    omega
  · have hp := hΓc.precedes_of_intervalPrecedes hfree hΛc ⟨hs, by omega, by omega⟩
    exact ha Γ hΓ Λ hΛ hp.isLinked

/-- In an unlinked multisegment, some segment begins at a given left end `ρ` of the
content and ends at a right end. -/
theorem exists_segment_at_left_end
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {a : Multisegment.{uV, uF} T} (ha : a.IsUnlinked) {ρ : CuspidalDatum.{uV, uF} T}
    (hρ : ρ ∈ a.cuspidalContent) (hleft : ρ.twist (-1 : ℝ) ∉ a.cuspidalContent) :
    ∃ Γ ∈ a, Γ.base = ρ ∧ ρ.twist (Γ.length : ℝ) ∉ a.cuspidalContent := by
  obtain ⟨Γ, hΓ, hΓρ, hmax⟩ := exists_longest_at_left_end hρ hleft
  subst hΓρ
  exact ⟨Γ, hΓ, rfl, twist_length_notMem hfree ha hΓ hleft hmax⟩

/-- Two segments of multisegments with the same content that begin at the same datum and
both end at a right end of that content are equal. -/
theorem eq_of_right_end {a b : Multisegment.{uV, uF} T}
    (hc : a.cuspidalContent = b.cuspidalContent) {Γ Λ : Segment.{uV, uF} T}
    (hΓ : Γ ∈ a) (hΛ : Λ ∈ b) (hb : Γ.base = Λ.base)
    (hΓr : Γ.base.twist (Γ.length : ℝ) ∉ a.cuspidalContent)
    (hΛr : Λ.base.twist (Λ.length : ℝ) ∉ b.cuspidalContent) : Γ = Λ := by
  refine Segment.ext_of_base_length hb ?_
  rcases lt_trichotomy Γ.length Λ.length with hl | hl | hl
  · exfalso
    apply hΓr
    rw [hc, hb]
    exact (Multisegment.mem_cuspidalContent_iff b _).mpr ⟨Λ, hΛ, Λ.member_mem_support hl⟩
  · exact hl
  · exfalso
    apply hΛr
    rw [← hc, ← hb]
    exact (Multisegment.mem_cuspidalContent_iff a _).mpr ⟨Γ, hΓ, Γ.member_mem_support hl⟩

end UnlinkedReconstruction

end Langlands.PadicField.TopologicalData

namespace Langlands.Classification

universe uF uV

open PadicField.TopologicalData PadicField.TopologicalData.UnlinkedReconstruction in
/-- Unlinked multisegments with equal cuspidal content are equal. -/
theorem unlinkedCuspidalContentInjectivity
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    UnlinkedCuspidalContentInjectivity.{uF,uV} F T := by
  classical
  have hfree := cuspidalIntegralTwistFreeness.{uF,uV} F T
  suffices h : ∀ (n : ℕ) (a b : T.Multisegment.{uV,uF}), Multiset.card a = n →
      a.IsUnlinked → b.IsUnlinked → a.cuspidalContent = b.cuspidalContent → a = b from
    fun a b => h _ a b rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hn ha hb hc
    by_cases ha0 : a = 0
    · subst ha0
      rw [Multisegment.cuspidalContent_zero, eq_comm,
        Multisegment.cuspidalContent_eq_zero_iff] at hc
      exact hc.symm
    obtain ⟨Δ, hΔ⟩ := Multiset.exists_mem_of_ne_zero ha0
    obtain ⟨ρ, hρ, hleft⟩ := exists_left_end hfree a.cuspidalContent
      ((Multisegment.mem_cuspidalContent_iff a Δ.base).mpr ⟨Δ, hΔ, Δ.base_mem_support⟩)
    obtain ⟨Γ, hΓ, hΓρ, hΓr⟩ := exists_segment_at_left_end hfree ha hρ hleft
    obtain ⟨Λ, hΛ, hΛρ, hΛr⟩ :=
      exists_segment_at_left_end hfree hb (hc ▸ hρ) (hc ▸ hleft)
    have hΓΛ : Γ = Λ :=
      eq_of_right_end hc hΓ hΛ (hΓρ.trans hΛρ.symm) (hΓρ ▸ hΓr) (hΛρ ▸ hΛr)
    subst hΓΛ
    have hca := congrArg Multisegment.cuspidalContent (Multiset.cons_erase hΓ)
    have hcb := congrArg Multisegment.cuspidalContent (Multiset.cons_erase hΛ)
    rw [Multisegment.cuspidalContent_cons] at hca hcb
    have hrest : Multisegment.cuspidalContent (a.erase Γ) =
        Multisegment.cuspidalContent (b.erase Γ) :=
      add_left_cancel (hca.trans (hc.trans hcb.symm))
    have hlt : Multiset.card (a.erase Γ) < n := hn ▸ Multiset.card_erase_lt_of_mem hΓ
    have heq := ih _ hlt (a.erase Γ) (b.erase Γ) rfl
      (ha.of_le (Multiset.erase_le Γ a)) (hb.of_le (Multiset.erase_le Γ b)) hrest
    rw [← Multiset.cons_erase hΓ, ← Multiset.cons_erase hΛ, heq]

end Langlands.Classification
