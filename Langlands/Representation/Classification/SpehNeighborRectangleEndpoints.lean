import Langlands.Representation.Classification.SpehNeighborRankGeometry

/-! # Endpoints of the transposed neighboring Speh rectangles -/

noncomputable section

namespace Langlands.Classification

open PadicField.TopologicalData
open scoped Classical

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- The end of a centered segment has the opposite half-length shift. -/
theorem tadicCenteredSegment_last (ρ : T.CuspidalDatum.{uV, uF})
    (d : ℕ) (hd : 0 < d) (x : ℝ) :
    (tadicCenteredSegment ρ d hd x).last = ρ.twist (x + ((d : ℝ) - 1) / 2) := by
  simp only [Segment.last, Segment.member, tadicCenteredSegment, CuspidalDatum.twist_twist]
  congr 1
  rw [Nat.cast_sub (by omega : 1 ≤ d)]
  push_cast
  ring

/-- The beginning occurrences of a centered rectangle. -/
theorem beginnings_tadicMultisegment (ρ : T.CuspidalDatum.{uV, uF})
    (n d : ℕ) (hd : 0 < d) :
    Multisegment.beginnings (tadicMultisegment ρ n d hd) =
      (Multiset.range n).map (fun j : ℕ =>
        ρ.twist ((j : ℝ) - ((n : ℝ) - 1) / 2 - ((d : ℝ) - 1) / 2)) := by
  simp only [Multisegment.beginnings, tadicMultisegment, Multiset.map_map,
    Function.comp_def, tadicCenteredSegment]

/-- The ending occurrences of a centered rectangle. -/
theorem endings_tadicMultisegment (ρ : T.CuspidalDatum.{uV, uF})
    (n d : ℕ) (hd : 0 < d) :
    Multisegment.endings (tadicMultisegment ρ n d hd) =
      (Multiset.range n).map (fun j : ℕ =>
        ρ.twist ((j : ℝ) - ((n : ℝ) - 1) / 2 + ((d : ℝ) - 1) / 2)) := by
  simp only [Multisegment.endings, tadicMultisegment, Multiset.map_map,
    Function.comp_def, tadicCenteredSegment_last]

/-- The two ending ranges are shifted by one, and meet in the interior. -/
theorem endings_neighbor_rectangles (ρ : T.CuspidalDatum.{uV, uF})
    (l k : ℕ) (hk : 2 ≤ k) :
    let x : ℝ := ((k : ℝ) - l - 1) / 2
    Multisegment.endings
        (tadicMultisegment ρ l (k + 1) (by omega) +
          tadicMultisegment ρ l (k - 1) (by omega)) =
      (Multiset.range l).map (fun j : ℕ => ρ.twist (x + (j + 1 : ℕ))) +
        (Multiset.range l).map (fun j : ℕ => ρ.twist (x + j)) := by
  dsimp only
  rw [Multisegment.endings, Multiset.map_add]
  change Multisegment.endings (tadicMultisegment ρ l (k + 1) _) +
    Multisegment.endings (tadicMultisegment ρ l (k - 1) _) = _
  rw [endings_tadicMultisegment, endings_tadicMultisegment]
  congr 2 <;> funext j <;> congr 1
  · push_cast
    ring
  · rw [Nat.cast_sub (by omega : 1 ≤ k)]
    push_cast
    ring

/-- The two beginning ranges have the same interior multiplicity pattern. -/
theorem beginnings_neighbor_rectangles (ρ : T.CuspidalDatum.{uV, uF})
    (l k : ℕ) (hk : 2 ≤ k) :
    let y : ℝ := (-(k : ℝ) - l + 1) / 2
    Multisegment.beginnings
        (tadicMultisegment ρ l (k + 1) (by omega) +
          tadicMultisegment ρ l (k - 1) (by omega)) =
      (Multiset.range l).map (fun j : ℕ => ρ.twist (y + j)) +
        (Multiset.range l).map (fun j : ℕ => ρ.twist (y + (j + 1 : ℕ))) := by
  dsimp only
  rw [Multisegment.beginnings, Multiset.map_add]
  change Multisegment.beginnings (tadicMultisegment ρ l (k + 1) _) +
    Multisegment.beginnings (tadicMultisegment ρ l (k - 1) _) = _
  rw [beginnings_tadicMultisegment, beginnings_tadicMultisegment]
  congr 2 <;> funext j <;> congr 1
  · push_cast
    ring
  · rw [Nat.cast_sub (by omega : 1 ≤ k)]
    push_cast
    ring

/-- Natural coordinates on a real cuspidal line are distinct. -/
theorem cuspidalDatum_natLine_injective (ρ : T.CuspidalDatum.{uV, uF}) (x : ℝ) :
    Function.Injective (fun j : ℕ => ρ.twist (x + j)) := by
  intro i j he
  have hx := cuspidalDatum_twist_injective ρ he
  have hij : (i : ℝ) = j := by linarith
  exact_mod_cast hij

/-- All endings have integral indices between zero and `l`. -/
theorem ending_index_neighbor_rectangles (ρ : T.CuspidalDatum.{uV, uF})
    (l k : ℕ) (hk : 2 ≤ k) :
    let x : ℝ := ((k : ℝ) - l - 1) / 2
    ∀ Δ ∈ tadicMultisegment ρ l (k + 1) (by omega) +
        tadicMultisegment ρ l (k - 1) (by omega),
      ∃ j ≤ l, Δ.last = ρ.twist (x + j) := by
  dsimp only
  intro Δ hΔ
  have hm : Δ.last ∈ Multisegment.endings
      (tadicMultisegment ρ l (k + 1) (by omega) +
        tadicMultisegment ρ l (k - 1) (by omega)) :=
    Multiset.mem_map.mpr ⟨Δ, hΔ, rfl⟩
  rw [endings_neighbor_rectangles ρ l k hk] at hm
  rcases Multiset.mem_add.mp hm with hm | hm
  · obtain ⟨j, hj, he⟩ := Multiset.mem_map.mp hm
    exact ⟨j + 1, by have := Multiset.mem_range.mp hj; omega, he.symm⟩
  · obtain ⟨j, hj, he⟩ := Multiset.mem_map.mp hm
    exact ⟨j, le_of_lt (Multiset.mem_range.mp hj), he.symm⟩

/-- All endings of the two rectangles are bounded by their greatest ending. -/
theorem ending_le_neighbor_rectangles (ρ : T.CuspidalDatum.{uV, uF})
    (l k : ℕ) (hk : 2 ≤ k) :
    let x : ℝ := ((k : ℝ) - l - 1) / 2
    ∀ Δ ∈ tadicMultisegment ρ l (k + 1) (by omega) +
        tadicMultisegment ρ l (k - 1) (by omega),
      ∃ e ≤ x + l, Δ.last = ρ.twist e := by
  dsimp only
  intro Δ hΔ
  have hm : Δ.last ∈ Multisegment.endings
      (tadicMultisegment ρ l (k + 1) (by omega) +
        tadicMultisegment ρ l (k - 1) (by omega)) :=
    Multiset.mem_map.mpr ⟨Δ, hΔ, rfl⟩
  rw [endings_neighbor_rectangles ρ l k hk] at hm
  rcases Multiset.mem_add.mp hm with hm | hm
  · obtain ⟨j, hj, he⟩ := Multiset.mem_map.mp hm
    have hj : j + 1 ≤ l := by have := Multiset.mem_range.mp hj; omega
    refine ⟨_, ?_, he.symm⟩
    have hj' : ((j + 1 : ℕ) : ℝ) ≤ l := by exact_mod_cast hj
    linarith
  · obtain ⟨j, hj, he⟩ := Multiset.mem_map.mp hm
    have hj : j ≤ l := le_of_lt (Multiset.mem_range.mp hj)
    refine ⟨_, ?_, he.symm⟩
    have hj' : (j : ℝ) ≤ l := by exact_mod_cast hj
    linarith

/-- The greatest ending occurs at most once, even with all interior
multiplicities retained. -/
theorem top_ending_count_neighbor_rectangles (ρ : T.CuspidalDatum.{uV, uF})
    (l k : ℕ) (hk : 2 ≤ k) :
    let x : ℝ := ((k : ℝ) - l - 1) / 2
    (Multisegment.endings
      (tadicMultisegment ρ l (k + 1) (by omega) +
        tadicMultisegment ρ l (k - 1) (by omega))).count (ρ.twist (x + l)) ≤ 1 := by
  dsimp only
  rw [endings_neighbor_rectangles ρ l k hk, Multiset.count_add]
  let x : ℝ := ((k : ℝ) - l - 1) / 2
  have hinj : Function.Injective (fun j : ℕ => ρ.twist (x + (j + 1 : ℕ))) := by
    intro i j he
    have h := cuspidalDatum_natLine_injective ρ x he
    omega
  have hfirst := Multiset.nodup_iff_count_le_one.mp
    (Multiset.Nodup.map hinj (Multiset.nodup_range l)) (ρ.twist (x + l))
  have hsecond : ((Multiset.range l).map (fun j : ℕ => ρ.twist (x + j))).count
      (ρ.twist (x + l)) = 0 := by
    apply Multiset.count_eq_zero_of_notMem
    rintro hm
    obtain ⟨j, hj, he⟩ := Multiset.mem_map.mp hm
    have h := cuspidalDatum_natLine_injective ρ x he
    have := Multiset.mem_range.mp hj
    omega
  dsimp only [x] at hfirst hsecond
  omega

/-- All beginnings have integral indices between zero and `l`. -/
theorem beginning_index_neighbor_rectangles (ρ : T.CuspidalDatum.{uV, uF})
    (l k : ℕ) (hk : 2 ≤ k) :
    let y : ℝ := (-(k : ℝ) - l + 1) / 2
    ∀ Δ ∈ tadicMultisegment ρ l (k + 1) (by omega) +
        tadicMultisegment ρ l (k - 1) (by omega),
      ∃ j ≤ l, Δ.base = ρ.twist (y + j) := by
  dsimp only
  intro Δ hΔ
  have hm : Δ.base ∈ Multisegment.beginnings
      (tadicMultisegment ρ l (k + 1) (by omega) +
        tadicMultisegment ρ l (k - 1) (by omega)) :=
    Multiset.mem_map.mpr ⟨Δ, hΔ, rfl⟩
  rw [beginnings_neighbor_rectangles ρ l k hk] at hm
  rcases Multiset.mem_add.mp hm with hm | hm
  · obtain ⟨j, hj, he⟩ := Multiset.mem_map.mp hm
    exact ⟨j, le_of_lt (Multiset.mem_range.mp hj), he.symm⟩
  · obtain ⟨j, hj, he⟩ := Multiset.mem_map.mp hm
    exact ⟨j + 1, by have := Multiset.mem_range.mp hj; omega, he.symm⟩

/-- The original segment at the greatest ending begins at index `l-1`,
strictly below the exceptional greatest beginning. -/
theorem exists_top_segment_neighbor_rectangles (ρ : T.CuspidalDatum.{uV, uF})
    (l k : ℕ) (hl : 0 < l) (hk : 2 ≤ k) :
    let x : ℝ := ((k : ℝ) - l - 1) / 2
    let y : ℝ := (-(k : ℝ) - l + 1) / 2
    ∃ Δ ∈ tadicMultisegment ρ l (k + 1) (by omega) +
        tadicMultisegment ρ l (k - 1) (by omega),
      Δ.last = ρ.twist (x + l) ∧ Δ.base = ρ.twist (y + (l - 1 : ℕ)) := by
  dsimp only
  let Δ := tadicCenteredSegment ρ (k + 1) (by omega)
    (((l - 1 : ℕ) : ℝ) - ((l : ℝ) - 1) / 2)
  refine ⟨Δ, Multiset.mem_add.mpr (Or.inl ?_), ?_, ?_⟩
  · exact Multiset.mem_map.mpr ⟨l - 1, Multiset.mem_range.mpr (by omega), rfl⟩
  · dsimp only [Δ]
    rw [tadicCenteredSegment_last]
    congr 1
    rw [Nat.cast_sub (by omega : 1 ≤ l)]
    push_cast
    ring
  · change ρ.twist _ = ρ.twist _
    congr 1
    rw [Nat.cast_sub (by omega : 1 ≤ l)]
    push_cast
    ring

/-- The first descending-beginning chain in any rank-lower multisegment of
the two rectangles has at most `l` terms. -/
theorem first_chain_length_le_neighbor_rectangles
    (ρ : T.CuspidalDatum.{uV, uF}) (l k : ℕ) (hl : 0 < l) (hk : 2 ≤ k)
    {b : T.Multisegment.{uV, uF}}
    (h : Multisegment.RankLE b
      (tadicMultisegment ρ l (k + 1) (by omega) +
        tadicMultisegment ρ l (k - 1) (by omega)))
    {r : ℕ} (hr : 0 < r) (δ : Fin r → T.Segment.{uV, uF})
    (hδ : ∀ i, δ i ∈ b)
    (hfirst : (δ ⟨0, hr⟩).last = ρ.twist ((((k : ℝ) - l - 1) / 2) + l))
    (hchain : ∀ i j, i < j → ∃ s : ℝ, 0 < s ∧
      (δ i).base = (δ j).base.twist s) : r ≤ l := by
  let y : ℝ := (-(k : ℝ) - l + 1) / 2
  have hb : ∀ Γ ∈ b, ∃ j ≤ l, Γ.base = ρ.twist (y + j) := by
    intro Γ hΓ
    have hm := Multiset.mem_of_le h.beginnings_le
      (Multiset.mem_map.mpr ⟨Γ, hΓ, rfl⟩)
    obtain ⟨J, hJ, heJ⟩ := Multiset.mem_map.mp hm
    obtain ⟨j, hj, he⟩ := beginning_index_neighbor_rectangles ρ l k hk J hJ
    exact ⟨j, hj, heJ.symm.trans he⟩
  obtain ⟨Δ, hΔ, heΔ, hbΔ⟩ := exists_top_segment_neighbor_rectangles ρ l k hl hk
  have hf := h.beginning_index_lt_of_unique_top_ending
    (ending_le_neighbor_rectangles ρ l k hk)
    (top_ending_count_neighbor_rectangles ρ l k hk)
    (beginning_index_neighbor_rectangles ρ l k hk)
    hΔ heΔ hbΔ (by omega : l - 1 < l) (hδ ⟨0, hr⟩) hfirst
  exact Multisegment.chain_length_le_of_beginning_indices hr hb δ hδ hf hchain

/-- The greatest original ending remains present in every rank-lower
multisegment of the neighboring rectangles. -/
theorem exists_top_ending_of_rankLE_neighbor_rectangles
    (ρ : T.CuspidalDatum.{uV, uF}) (l k : ℕ) (hl : 0 < l) (hk : 2 ≤ k)
    {b : T.Multisegment.{uV, uF}}
    (h : Multisegment.RankLE b
      (tadicMultisegment ρ l (k + 1) (by omega) +
        tadicMultisegment ρ l (k - 1) (by omega))) :
    ∃ Γ ∈ b, Γ.last = ρ.twist ((((k : ℝ) - l - 1) / 2) + l) := by
  obtain ⟨Δ, hΔ, heΔ, -⟩ := exists_top_segment_neighbor_rectangles ρ l k hl hk
  exact h.exists_top_ending (ending_le_neighbor_rectangles ρ l k hk) hΔ heΔ

/-- After shortening the first consecutive-ending, descending-beginning
chain, every remaining ending lies in an interval of `l` points. -/
theorem first_step_ending_bound_neighbor_rectangles
    (ρ : T.CuspidalDatum.{uV, uF}) (l k : ℕ) (hl : 0 < l) (hk : 2 ≤ k)
    {b c : T.Multisegment.{uV, uF}}
    (h : Multisegment.RankLE b
      (tadicMultisegment ρ l (k + 1) (by omega) +
        tadicMultisegment ρ l (k - 1) (by omega)))
    {r : ℕ} (hr : 0 < r) (δ : Fin r → T.Segment.{uV, uF})
    (hdecomp : b = c + (List.ofFn δ : Multiset _))
    (hends : ∀ i, (δ i).last =
      ρ.twist ((((k : ℝ) - l - 1) / 2) + l - (i.val : ℝ)))
    (hchain : ∀ i j, i < j → ∃ s : ℝ, 0 < s ∧
      (δ i).base = (δ j).base.twist s) :
    r ≤ l ∧
      ∀ Γ ∈ c + Multisegment.dropLast (List.ofFn δ : Multiset _),
        ∃ j < l, Γ.last = ρ.twist ((((k : ℝ) - l - 1) / 2) + j) := by
  let x : ℝ := ((k : ℝ) - l - 1) / 2
  have hδ : ∀ i, δ i ∈ b := by
    intro i
    rw [hdecomp]
    exact Multiset.mem_add.mpr (Or.inr
      (Multiset.mem_coe.mpr (List.mem_ofFn.mpr ⟨i, rfl⟩)))
  have hfirst : (δ ⟨0, hr⟩).last = ρ.twist (x + l) := by
    simpa only [Nat.cast_zero, sub_zero] using hends ⟨0, hr⟩
  have hrl := first_chain_length_le_neighbor_rectangles ρ l k hl hk h hr δ hδ hfirst hchain
  refine ⟨hrl, ?_⟩
  apply Multisegment.ending_indices_after_selected_dropLast
  · intro Γ hΓ
    have hΓb : Γ ∈ b := by rw [hdecomp]; exact hΓ
    have hm := Multiset.mem_of_le h.endings_le
      (Multiset.mem_map.mpr ⟨Γ, hΓb, rfl⟩)
    obtain ⟨J, hJ, heJ⟩ := Multiset.mem_map.mp hm
    obtain ⟨j, hj, he⟩ := ending_index_neighbor_rectangles ρ l k hk J hJ
    exact ⟨j, hj, heJ.symm.trans he⟩
  · rw [← hdecomp]
    exact (Multiset.le_iff_count.mp h.endings_le _).trans
      (top_ending_count_neighbor_rectangles ρ l k hk)
  · exact ⟨δ ⟨0, hr⟩, Multiset.mem_coe.mpr (List.mem_ofFn.mpr ⟨⟨0, hr⟩, rfl⟩), hfirst⟩
  · intro Γ hΓ
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (Multiset.mem_coe.mp hΓ)
    have hi : i.val < l := lt_of_lt_of_le i.isLt hrl
    refine ⟨l - i.val, by omega, by omega, ?_⟩
    rw [hends]
    congr 1
    rw [Nat.cast_sub (by omega : i.val ≤ l)]
    ring

end Langlands.Classification
