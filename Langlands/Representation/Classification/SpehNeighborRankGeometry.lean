import Langlands.Representation.Classification.TadicSpehHeads
import Langlands.Representation.Aubert.RankOrderEndpoints
import Langlands.Representation.Aubert.SegmentEndDerivation

/-! # Endpoint geometry for the neighboring Speh argument -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

universe uF uV

open scoped Classical

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace Segment

/-- A member on a real cuspidal line lies no later than its segment's end. -/
theorem coordinate_le_last_of_mem_support {ρ : T.CuspidalDatum.{uV, uF}}
    {s t : ℝ} {Δ : T.Segment.{uV, uF}}
    (hs : ρ.twist s ∈ Δ.support) (ht : Δ.last = ρ.twist t) : s ≤ t := by
  obtain ⟨i, hi, hmem⟩ := hs
  have he : Δ.last = (Δ.member i).twist (((Δ.length - 1 : ℕ) : ℝ) - i) := by
    simp only [last, member, CuspidalDatum.twist_twist]
    congr 1
    ring
  rw [hmem, CuspidalDatum.twist_twist] at he
  have hx := Classification.cuspidalDatum_twist_injective ρ (he.symm.trans ht)
  have hi' : (i : ℝ) ≤ ((Δ.length - 1 : ℕ) : ℝ) := by exact_mod_cast (show i ≤ Δ.length - 1 by omega)
  linarith

/-- Inclusion of segments on an integral translate line can only move a beginning
leftwards. -/
theorem beginning_index_le_of_support_subset {ρ : T.CuspidalDatum.{uV, uF}}
    {y : ℝ} {i j : ℕ} {Δ Γ : T.Segment.{uV, uF}}
    (hsub : Δ.support ⊆ Γ.support)
    (hΔ : Δ.base = ρ.twist (y + i)) (hΓ : Γ.base = ρ.twist (y + j)) : j ≤ i := by
  obtain ⟨r, hr, -⟩ := support_subset_iff.mp hsub
  change Δ.base = Γ.base.twist (r : ℝ) at hr
  rw [hΔ, hΓ, CuspidalDatum.twist_twist] at hr
  have hx := Classification.cuspidalDatum_twist_injective ρ hr
  have hx' : (j : ℝ) ≤ i := by have hr' : (0 : ℝ) ≤ r := Nat.cast_nonneg r; linarith
  exact_mod_cast hx'

/-- A nonempty right truncation moves the ending back by one twist. -/
theorem last_of_dropLast_eq_some {Δ Γ : T.Segment.{uV, uF}}
    (hdrop : Δ.dropLast = some Γ) : Γ.last = Δ.last.twist (-1) := by
  by_cases hlen : 1 < Δ.length
  · rw [Δ.dropLast_of_one_lt hlen] at hdrop
    rw [← Option.some.inj hdrop]
    exact Aubert.SegmentEndDerivation.last_shorten Δ hlen
  · have hone : Δ.length = 1 := by have := Δ.length_pos; omega
    rw [Δ.dropLast_of_length_eq_one hone] at hdrop
    contradiction

end Segment

namespace Multisegment

/-- A rank-lower multisegment contains a segment covering each original segment. -/
theorem RankLE.exists_containing {a b : T.Multisegment.{uV, uF}}
    (h : RankLE b a) {Δ : T.Segment.{uV, uF}} (hΔ : Δ ∈ a) :
    ∃ Γ ∈ b, Δ.support ⊆ Γ.support := by
  apply (containmentCount_pos_iff Δ b).mp
  exact lt_of_lt_of_le ((containmentCount_pos_iff Δ a).mpr ⟨Δ, hΔ, Set.Subset.rfl⟩) (h.2 Δ)

/-- An original greatest ending persists under rank lowering. -/
theorem RankLE.exists_top_ending {a b : T.Multisegment.{uV, uF}}
    (h : RankLE b a) {ρ : T.CuspidalDatum.{uV, uF}} {top : ℝ}
    (ha : ∀ Γ ∈ a, ∃ t ≤ top, Γ.last = ρ.twist t)
    {Δ : T.Segment.{uV, uF}} (hΔ : Δ ∈ a) (heΔ : Δ.last = ρ.twist top) :
    ∃ Γ ∈ b, Γ.last = ρ.twist top := by
  obtain ⟨Γ, hΓ, hsub⟩ := h.exists_containing hΔ
  have hm := Multiset.mem_of_le h.endings_le
    (Multiset.mem_map.mpr ⟨Γ, hΓ, rfl⟩)
  obtain ⟨J, hJ, heJ⟩ := Multiset.mem_map.mp hm
  obtain ⟨t, ht, he⟩ := ha J hJ
  have heΓ : Γ.last = ρ.twist t := heJ.symm.trans he
  have hle := Segment.coordinate_le_last_of_mem_support
    (hsub (heΔ ▸ Δ.last_mem_support)) heΓ
  exact ⟨Γ, hΓ, by rw [heΓ, le_antisymm ht hle]⟩

/-- At an ending whose occurrence count is at most one, two segments must agree. -/
theorem eq_of_last_eq_of_endings_count_le_one {a : T.Multisegment.{uV, uF}}
    {Δ Γ : T.Segment.{uV, uF}} (hΔ : Δ ∈ a) (hΓ : Γ ∈ a)
    (he : Δ.last = Γ.last) (hc : (endings a).count Δ.last ≤ 1) : Δ = Γ := by
  classical
  obtain ⟨a, rfl⟩ := Multiset.exists_cons_of_mem hΔ
  by_contra hne
  have hΓ' : Γ ∈ a := by simpa [Ne.symm hne] using hΓ
  have hp : 0 < (endings a).count Δ.last := Multiset.count_pos.mpr
    (Multiset.mem_map.mpr ⟨Γ, hΓ', he.symm⟩)
  simp only [endings, Multiset.map_cons, Multiset.count_cons_self] at hc
  change 0 < (a.map Segment.last).count Δ.last at hp
  omega

/-- The segment at a unique greatest ending contains the original segment at that
ending, even after passing to an arbitrary rank-lower multisegment. -/
theorem RankLE.contains_of_unique_top_ending {a b : T.Multisegment.{uV, uF}}
    (h : RankLE b a) {ρ : T.CuspidalDatum.{uV, uF}} {top : ℝ}
    (ha : ∀ Γ ∈ a, ∃ t ≤ top, Γ.last = ρ.twist t)
    (hc : (endings a).count (ρ.twist top) ≤ 1)
    {Δ Γ : T.Segment.{uV, uF}} (hΔ : Δ ∈ a) (heΔ : Δ.last = ρ.twist top)
    (hΓ : Γ ∈ b) (heΓ : Γ.last = ρ.twist top) : Δ.support ⊆ Γ.support := by
  classical
  obtain ⟨J, hJ, hsub⟩ := h.exists_containing hΔ
  have hm : J.last ∈ endings a := Multiset.mem_of_le h.endings_le
    (Multiset.mem_map.mpr ⟨J, hJ, rfl⟩)
  obtain ⟨J', hJ', heJ'⟩ := Multiset.mem_map.mp hm
  obtain ⟨t, ht, heJ⟩ := ha J' hJ'
  have heJ : J.last = ρ.twist t := heJ'.symm.trans heJ
  have htop : ρ.twist top ∈ J.support := hsub (heΔ ▸ Δ.last_mem_support)
  have hle := Segment.coordinate_le_last_of_mem_support htop heJ
  have heq : J.last = ρ.twist top := by rw [heJ, le_antisymm ht hle]
  have hc' : (endings b).count J.last ≤ 1 := by
    rw [heq]
    exact (Multiset.le_iff_count.mp h.endings_le _).trans hc
  have hsame : J = Γ := eq_of_last_eq_of_endings_count_le_one hJ hΓ
    (heq.trans heΓ.symm) hc'
  exact hsame ▸ hsub

/-- The beginning at the greatest ending avoids the exceptional greatest
beginning coordinate in the neighboring-rectangle configuration. -/
theorem RankLE.beginning_index_lt_of_unique_top_ending
    {a b : T.Multisegment.{uV, uF}} (h : RankLE b a)
    {ρ : T.CuspidalDatum.{uV, uF}} {top y : ℝ} {l t : ℕ}
    (ha : ∀ Γ ∈ a, ∃ e ≤ top, Γ.last = ρ.twist e)
    (hc : (endings a).count (ρ.twist top) ≤ 1)
    (hb : ∀ Γ ∈ a, ∃ j ≤ l, Γ.base = ρ.twist (y + j))
    {Δ Γ : T.Segment.{uV, uF}} (hΔ : Δ ∈ a) (heΔ : Δ.last = ρ.twist top)
    (hbΔ : Δ.base = ρ.twist (y + t)) (ht : t < l)
    (hΓ : Γ ∈ b) (heΓ : Γ.last = ρ.twist top) :
    ∃ j < l, Γ.base = ρ.twist (y + j) := by
  have hm : Γ.base ∈ beginnings a := Multiset.mem_of_le h.beginnings_le
    (Multiset.mem_map.mpr ⟨Γ, hΓ, rfl⟩)
  obtain ⟨J, hJ, heJ⟩ := Multiset.mem_map.mp hm
  obtain ⟨j, -, hj⟩ := hb J hJ
  have hΓb : Γ.base = ρ.twist (y + j) := heJ.symm.trans hj
  have hsub := h.contains_of_unique_top_ending ha hc hΔ heΔ hΓ heΓ
  exact ⟨j, lt_of_le_of_lt (Segment.beginning_index_le_of_support_subset hsub hbΔ hΓb) ht, hΓb⟩

/-- A chain with strictly decreasing beginnings, whose first beginning avoids
index `l`, has at most `l` terms. The positive real twists encode the actual
strict ordering of the beginnings without ordering cuspidal classes. -/
theorem chain_length_le_of_beginning_indices
    {b : T.Multisegment.{uV, uF}} {ρ : T.CuspidalDatum.{uV, uF}}
    {y : ℝ} {l r : ℕ} (hr : 0 < r)
    (hb : ∀ Γ ∈ b, ∃ j ≤ l, Γ.base = ρ.twist (y + j))
    (δ : Fin r → T.Segment.{uV, uF}) (hδ : ∀ i, δ i ∈ b)
    (hfirst : ∃ j < l, (δ ⟨0, hr⟩).base = ρ.twist (y + j))
    (hchain : ∀ i j, i < j → ∃ s : ℝ, 0 < s ∧ (δ i).base = (δ j).base.twist s) :
    r ≤ l := by
  classical
  let f : Fin r → ℕ := fun i => (hb (δ i) (hδ i)).choose
  have hf : ∀ i, (δ i).base = ρ.twist (y + f i) :=
    fun i => (hb (δ i) (hδ i)).choose_spec.2
  have hanti : StrictAnti f := by
    intro i j hij
    obtain ⟨s, hs, he⟩ := hchain i j hij
    rw [hf i, hf j, CuspidalDatum.twist_twist] at he
    have hx := Classification.cuspidalDatum_twist_injective ρ he
    have hlt : (f j : ℝ) < f i := by linarith
    exact_mod_cast hlt
  obtain ⟨j, hj, hfirst⟩ := hfirst
  have hzero : f ⟨0, hr⟩ = j := by
    have hx := Classification.cuspidalDatum_twist_injective ρ ((hf ⟨0, hr⟩).symm.trans hfirst)
    have he : (f ⟨0, hr⟩ : ℝ) = j := by linarith
    exact_mod_cast he
  have hbound : ∀ i, f i < l := by
    intro i
    have hz : (⟨0, hr⟩ : Fin r) ≤ i := Nat.zero_le i.val
    exact lt_of_le_of_lt (hanti.antitone hz) (hzero ▸ hj)
  let g : Fin r → Fin l := fun i => ⟨f i, hbound i⟩
  have hginj : Function.Injective g := by
    intro i j he
    exact hanti.injective (congrArg Fin.val he)
  simpa using Fintype.card_le_of_injective g hginj

/-- Shortening selected segments whose endings have positive indices removes
a unique top ending and leaves all endings in the shorter index interval. -/
theorem ending_indices_after_selected_dropLast
    {c S : T.Multisegment.{uV, uF}} {ρ : T.CuspidalDatum.{uV, uF}}
    {x : ℝ} {l : ℕ}
    (hb : ∀ Δ ∈ c + S, ∃ j ≤ l, Δ.last = ρ.twist (x + j))
    (hc : (endings (c + S)).count (ρ.twist (x + l)) ≤ 1)
    (htop : ∃ Δ ∈ S, Δ.last = ρ.twist (x + l))
    (hS : ∀ Δ ∈ S, ∃ j, 0 < j ∧ j ≤ l ∧ Δ.last = ρ.twist (x + j)) :
    ∀ Γ ∈ c + S.dropLast, ∃ j < l, Γ.last = ρ.twist (x + j) := by
  classical
  have hnot : ρ.twist (x + l) ∉ endings c := by
    intro hm
    obtain ⟨Δ, hΔ, heΔ⟩ := htop
    have hp : 0 < (endings c).count (ρ.twist (x + l)) :=
      Multiset.count_pos.mpr hm
    have hq : 0 < (endings S).count (ρ.twist (x + l)) :=
      Multiset.count_pos.mpr (Multiset.mem_map.mpr ⟨Δ, hΔ, heΔ⟩)
    simp only [endings, Multiset.map_add, Multiset.count_add] at hc
    change 0 < (c.map Segment.last).count _ at hp
    change 0 < (S.map Segment.last).count _ at hq
    omega
  intro Γ hΓ
  rcases Multiset.mem_add.mp hΓ with hΓ | hΓ
  · obtain ⟨j, hj, heΓ⟩ := hb Γ (Multiset.mem_add.mpr (Or.inl hΓ))
    have hne : j ≠ l := by
      intro he
      apply hnot
      exact Multiset.mem_map.mpr ⟨Γ, hΓ, by simpa only [he] using heΓ⟩
    exact ⟨j, by omega, heΓ⟩
  · obtain ⟨Δ, hΔ, hdrop⟩ := (Multiset.mem_filterMap Segment.dropLast S).mp hΓ
    obtain ⟨j, hj, hjl, heΔ⟩ := hS Δ hΔ
    refine ⟨j - 1, by omega, ?_⟩
    rw [Segment.last_of_dropLast_eq_some hdrop, heΔ, CuspidalDatum.twist_twist]
    congr 1
    rw [Nat.cast_sub (by omega : 1 ≤ j)]
    push_cast
    ring

end Multisegment

end Langlands.PadicField.TopologicalData
