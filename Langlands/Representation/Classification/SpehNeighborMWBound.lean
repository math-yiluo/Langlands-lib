import Langlands.Representation.Classification.SpehNeighborRectangleEndpoints
import Langlands.Representation.Classification.MoeglinWaldspurgerRealization
import Langlands.Representation.Classification.MoeglinWaldspurgerStatements

/-! # The MW length bound for rank-lower neighboring rectangles -/

noncomputable section

namespace Langlands.MoeglinWaldspurger

open PadicField.TopologicalData
open scoped Classical

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- The first interval chosen in a round is an actual input occurrence. -/
theorem round_first_mem {a : Multisegment} {r : Round}
    (h : round a = some r) : r.first ∈ a := by
  rw [← round_partition h]
  exact Multiset.mem_add.mpr (Or.inl (by simp [Round.selected, Round.selectedList]))

/-- Descending lexicographic sorting gives the greatest ending first. -/
theorem round_ending_le_first {a : Multisegment} {r : Round}
    (h : round a = some r) {J : Interval} (hJ : J ∈ a) :
    J.ending ≤ r.first.ending := by
  unfold round at h
  cases hs : a.sort (fun I J => J ≤ I) with
  | nil => simp [hs] at h
  | cons I l =>
    simp only [hs, Option.some.injEq] at h
    subst r
    have hp := Multiset.pairwise_sort a (fun I J : Interval => J ≤ I)
    rw [hs] at hp
    have hm : J ∈ I :: l := by
      simpa only [hs] using (Multiset.mem_sort (fun I J : Interval => J ≤ I)).mpr hJ
    rcases List.mem_cons.mp hm with rfl | hm
    · exact le_rfl
    · have hle := (List.pairwise_cons.mp hp).1 J hm
      change toLex (J.ending, J.beginning) ≤ toLex (I.ending, I.beginning) at hle
      exact Prod.Lex.monotone_fst _ _ hle

/-- The emitted interval has one point per selected occurrence. -/
theorem Round.emitted_length (r : Round) :
    r.emitted.length = r.selectedList.length := by
  simp only [Round.emitted, Interval.length, Round.selectedList, List.length_cons]
  omega

/-- Realization commutes with shortening exactly the selected occurrences. -/
theorem realize_shorten (ρ : T.CuspidalDatum.{uV, uF}) (x : ℝ) (a : Multisegment) :
    realize ρ x (shorten a) =
      PadicField.TopologicalData.Multisegment.dropLast (realize ρ x a) := by
  induction a using Multiset.induction_on with
  | empty => rfl
  | cons I a ih =>
    simp only [shorten, Multiset.cons_bind, realize, Multiset.map_cons]
    change realize ρ x (I.dropLast + shorten a) =
      PadicField.TopologicalData.Multisegment.dropLast
        (I.realize ρ x ::ₘ realize ρ x a)
    rw [realize_add, ih]
    by_cases h : I.beginning < I.ending
    · have hlen : 1 < (I.realize ρ x).length := by
        simp only [Interval.realize_length, Interval.length]
        omega
      rw [PadicField.TopologicalData.Multisegment.dropLast_cons_of_one_lt _ hlen]
      simp only [Interval.dropLast, dite_eq_left h, realize, Multiset.map_singleton,
        Multiset.singleton_add]
      congr 1
      apply Segment.ext_base_length
      · rfl
      · simp only [Interval.realize_length, Segment.dropLastNonempty_length, Interval.length]
        omega
    · have hlen : (I.realize ρ x).length = 1 := by
        simp only [Interval.realize_length, Interval.length]
        have := I.nonempty
        omega
      rw [PadicField.TopologicalData.Multisegment.dropLast_cons_of_length_eq_one _ hlen]
      simp only [Interval.dropLast, dite_eq_right h, realize_zero, zero_add]

/-- Realizing the selected list as a finite family retains its multiplicities. -/
theorem realize_selected_eq_ofFn (ρ : T.CuspidalDatum.{uV, uF}) (x : ℝ) (r : Round) :
    realize ρ x r.selected =
      (List.ofFn (fun i : Fin r.selectedList.length =>
        (r.selectedList[i.val]).realize ρ x) : PadicField.TopologicalData.Multisegment T) := by
  simp only [List.ofFn_getElem_eq_map, realize, Round.selected, Multiset.map_coe]

/-- Inherited actual endings bound the integer endings of a realized label. -/
theorem ending_bounds_of_realize_rankLE_neighbor_rectangles
    (ρ : T.CuspidalDatum.{uV, uF}) (l k : ℕ) (hk : 2 ≤ k)
    {a : Multisegment}
    (h : PadicField.TopologicalData.Multisegment.RankLE
      (realize ρ (((k : ℝ) - l - 1) / 2) a)
      (Classification.tadicMultisegment ρ l (k + 1) (by omega) +
        Classification.tadicMultisegment ρ l (k - 1) (by omega))) :
    ∀ I ∈ a, 0 ≤ I.ending ∧ I.ending ≤ (l : ℤ) := by
  let x : ℝ := ((k : ℝ) - l - 1) / 2
  intro I hI
  have hIr : I.realize ρ x ∈ realize ρ x a :=
    Multiset.mem_map.mpr ⟨I, hI, rfl⟩
  have hm := Multiset.mem_of_le h.endings_le
    (Multiset.mem_map.mpr ⟨I.realize ρ x, hIr, rfl⟩)
  obtain ⟨Γ, hΓ, heΓ⟩ := Multiset.mem_map.mp hm
  obtain ⟨j, hj, hej⟩ :=
    Classification.ending_index_neighbor_rectangles ρ l k hk Γ hΓ
  have he : (I.realize ρ x).last = ρ.twist (x + (j : ℝ)) :=
    heΓ.symm.trans hej
  rw [Interval.realize_last] at he
  have hexp := Classification.cuspidalDatum_twist_injective ρ he
  dsimp only [x] at hexp
  have hij : (I.ending : ℝ) = (j : ℝ) := by linarith
  have hij' : I.ending = (j : ℤ) := by exact_mod_cast hij
  omega

/-- The greatest ending in a nonempty round is the inherited top endpoint. -/
theorem round_first_ending_neighbor_rectangles
    (ρ : T.CuspidalDatum.{uV, uF}) (l k : ℕ) (hl : 0 < l) (hk : 2 ≤ k)
    {a : Multisegment} {r : Round}
    (h : PadicField.TopologicalData.Multisegment.RankLE
      (realize ρ (((k : ℝ) - l - 1) / 2) a)
      (Classification.tadicMultisegment ρ l (k + 1) (by omega) +
        Classification.tadicMultisegment ρ l (k - 1) (by omega)))
    (hr : round a = some r) : r.first.ending = (l : ℤ) := by
  let x : ℝ := ((k : ℝ) - l - 1) / 2
  have hupper :=
    (ending_bounds_of_realize_rankLE_neighbor_rectangles ρ l k hk h
      r.first (round_first_mem hr)).2
  obtain ⟨Γ, hΓ, heΓ⟩ :=
    Classification.exists_top_ending_of_rankLE_neighbor_rectangles ρ l k hl hk h
  obtain ⟨I, hI, rfl⟩ := Multiset.mem_map.mp hΓ
  rw [Interval.realize_last] at heΓ
  have hexp := Classification.cuspidalDatum_twist_injective ρ heΓ
  have he : (I.ending : ℝ) = (l : ℝ) := by linarith
  have he' : I.ending = (l : ℤ) := by exact_mod_cast he
  have hlower := round_ending_le_first hr hI
  omega

/-- The actual first-step endpoint lemma applies to the selected MW occurrences. -/
theorem round_bound_neighbor_rectangles
    (ρ : T.CuspidalDatum.{uV, uF}) (l k : ℕ) (hl : 0 < l) (hk : 2 ≤ k)
    {a : Multisegment} {r : Round}
    (h : PadicField.TopologicalData.Multisegment.RankLE
      (realize ρ (((k : ℝ) - l - 1) / 2) a)
      (Classification.tadicMultisegment ρ l (k + 1) (by omega) +
        Classification.tadicMultisegment ρ l (k - 1) (by omega)))
    (hr : round a = some r) :
    r.selectedList.length ≤ l ∧
      ∀ I ∈ r.residual, 0 ≤ I.ending ∧ I.ending < (l : ℤ) := by
  let x : ℝ := ((k : ℝ) - l - 1) / 2
  let δ : Fin r.selectedList.length → T.Segment.{uV, uF} :=
    fun i => (r.selectedList[i.val]).realize ρ x
  have hpos : 0 < r.selectedList.length := by simp [Round.selectedList]
  have hfirst := round_first_ending_neighbor_rectangles ρ l k hl hk h hr
  have hselected : realize ρ x r.selected =
      (List.ofFn δ : PadicField.TopologicalData.Multisegment T) :=
    realize_selected_eq_ofFn ρ x r
  have hdecomp : realize ρ x a = realize ρ x r.untouched +
      (List.ofFn δ : PadicField.TopologicalData.Multisegment T) := by
    calc
      realize ρ x a = realize ρ x (r.selected + r.untouched) :=
        congrArg (realize ρ x) (round_partition hr).symm
      _ = realize ρ x r.untouched + realize ρ x r.selected := by
        rw [realize_add, add_comm]
      _ = _ := by rw [hselected]
  have hends : ∀ i, (δ i).last = ρ.twist (x + (l : ℝ) - (i.val : ℝ)) := by
    intro i
    change ((r.selectedList[i.val]).realize ρ x).last = _
    rw [Interval.realize_last, round_ending hr i.val i.isLt, hfirst]
    congr 1
    push_cast
    ring
  have hchain : ∀ i j, i < j → ∃ s : ℝ, 0 < s ∧
      (δ i).base = (δ j).base.twist s := by
    intro i j hij
    have hbegin :=
      (List.pairwise_iff_getElem.mp (round_decreasing hr))
        i.val j.val i.isLt j.isLt hij
    have hbegin' : ((r.selectedList[j.val]).beginning : ℝ) <
        ((r.selectedList[i.val]).beginning : ℝ) := by exact_mod_cast hbegin
    refine ⟨((r.selectedList[i.val]).beginning : ℝ) -
      ((r.selectedList[j.val]).beginning : ℝ), sub_pos.mpr hbegin', ?_⟩
    dsimp only [δ]
    simp only [Interval.realize_base, CuspidalDatum.twist_twist]
    congr 1
    ring
  obtain ⟨hlen, hres⟩ :=
    Classification.first_step_ending_bound_neighbor_rectangles
      ρ l k hl hk h hpos δ hdecomp hends hchain
  have hres_eq : realize ρ x r.residual = realize ρ x r.untouched +
      PadicField.TopologicalData.Multisegment.dropLast
        (List.ofFn δ : PadicField.TopologicalData.Multisegment T) := by
    rw [Round.residual, realize_add, realize_shorten, hselected]
  refine ⟨hlen, ?_⟩
  intro I hI
  have hm : I.realize ρ x ∈ realize ρ x r.residual :=
    Multiset.mem_map.mpr ⟨I, hI, rfl⟩
  rw [hres_eq] at hm
  obtain ⟨j, hj, he⟩ := hres (I.realize ρ x) hm
  rw [Interval.realize_last] at he
  have hexp := Classification.cuspidalDatum_twist_injective ρ he
  dsimp only [x] at hexp
  have hij : (I.ending : ℝ) = (j : ℝ) := by linarith
  have hij' : I.ending = (j : ℤ) := by exact_mod_cast hij
  omega

/-- Conditional use of Badulescu (P) after the controlled first MW round.
This does not prove `EndingBound`. -/
theorem dual_lengths_le_neighbor_rectangles (hP : EndingBound)
    (ρ : T.CuspidalDatum.{uV, uF}) (l k : ℕ) (hl : 0 < l) (hk : 2 ≤ k)
    {a : Multisegment}
    (h : PadicField.TopologicalData.Multisegment.RankLE
      (realize ρ (((k : ℝ) - l - 1) / 2) a)
      (Classification.tadicMultisegment ρ l (k + 1) (by omega) +
        Classification.tadicMultisegment ρ l (k - 1) (by omega))) :
    ∀ I ∈ dual a, I.length ≤ l := by
  cases hr : round a with
  | none =>
    have ha := (round_none_iff a).mp hr
    subst a
    simp
  | some r =>
    obtain ⟨hlen, hres⟩ := round_bound_neighbor_rectangles ρ l k hl hk h hr
    intro I hI
    rw [dual_of_round hr] at hI
    rcases Multiset.mem_cons.mp hI with rfl | hI
    · rw [Round.emitted_length]
      exact hlen
    · exact hP r.residual 0 l (by
        intro J hJ
        simpa only [zero_add] using hres J hJ) I hI

end Langlands.MoeglinWaldspurger
