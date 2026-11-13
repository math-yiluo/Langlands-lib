import Langlands.Representation.Classification.MoeglinWaldspurgerStatements

namespace Langlands.MoeglinWaldspurger

private abbrev entry (s : List Interval) (i : ℕ) : Interval :=
  s.getD i ⟨0, 0, le_rfl⟩

private theorem entry_eq (s : List Interval) (i : ℕ) (hi : i < s.length) :
    entry s i = s[i] := by
  simp [entry, List.getD_eq_getElem?_getD, hi]

private theorem entry_mem (s : List Interval) (i : ℕ) (hi : i < s.length) :
    entry s i ∈ s := by rw [entry_eq s i hi]; exact List.getElem_mem hi

private theorem order_ending {I J : Interval} (h : J ≤ I) : J.ending ≤ I.ending := by
  change toLex (J.ending, J.beginning) ≤ toLex (I.ending, I.beginning) at h
  have h' := Prod.Lex.le_iff.mp h
  dsimp at h'
  omega

private theorem order_beginning {I J : Interval} (h : J ≤ I)
    (he : J.ending = I.ending) : J.beginning ≤ I.beginning := by
  change toLex (J.ending, J.beginning) ≤ toLex (I.ending, I.beginning) at h
  have h' := Prod.Lex.le_iff.mp h
  dsimp at h'
  omega

private theorem sorted_head_max {a : Multisegment} {I : Interval} {l : List Interval}
    (hs : a.sort (fun I J => J ≤ I) = I :: l) {J : Interval} (hJ : J ∈ a) : J ≤ I := by
  have hp := Multiset.pairwise_sort a (fun I J : Interval => J ≤ I)
  rw [hs, List.pairwise_cons] at hp
  have hm : J ∈ I :: l := by rw [← hs]; exact (Multiset.mem_sort _).mpr hJ
  rcases List.mem_cons.mp hm with rfl | hm
  · exact le_rfl
  · exact hp.1 J hm

private theorem pick_exists_max {a : Multisegment} {e b : ℤ} {J : Interval}
    (hJ : J ∈ a) (he : J.ending = e) (hb : J.beginning < b) :
    ∃ I, pick a e b = some I ∧ J.beginning ≤ I.beginning := by
  let f := a.filter fun I => I.ending = e ∧ I.beginning < b
  have hf : J ∈ f := Multiset.mem_filter.mpr ⟨hJ, he, hb⟩
  cases hs : f.sort (fun I J => J ≤ I) with
  | nil =>
    have hm := (Multiset.mem_sort (fun I J : Interval => J ≤ I)).mpr hf
    simp [hs] at hm
  | cons I l =>
    have hp : pick a e b = some I := by simp [pick, f, hs]
    exact ⟨I, hp, order_beginning (sorted_head_max hs hf) (he.trans (pick_spec hp).1.symm)⟩

/-- The selected chain greedily dominates any eligible original interval,
including the assertion that its stopping position has no eligible interval. -/
private theorem chain_greedy (a : Multisegment) (e b : ℤ) (i : ℕ)
    (hi : i ≤ (chain a e b).1.length) {J : Interval}
    (hJ : J ∈ a) (he : J.ending = e - (i : ℤ))
    (hb : J.beginning < if i = 0 then b else (entry (chain a e b).1 (i - 1)).beginning) :
    i < (chain a e b).1.length ∧
      J.beginning ≤ (entry (chain a e b).1 i).beginning := by
  induction a using (measure (fun a : Multisegment => a.card)).wf.induction
      generalizing e b i with
  | h a ih =>
    generalize hc : chain a e b = result at hi hb ⊢
    rw [chain] at hc
    split at hc
    · rename_i hp
      subst result
      have hi0 : i = 0 := by simpa using hi
      subst i
      simp only [Nat.cast_zero, sub_zero] at he
      have hb' : J.beginning < b := by simpa using hb
      obtain ⟨I, hp', _⟩ := pick_exists_max hJ he hb'
      rw [hp] at hp'
      contradiction
    · rename_i I hp
      subst result
      cases i with
      | zero =>
        have hb' : J.beginning < b := by simpa using hb
        obtain ⟨I', hp', hmax⟩ := pick_exists_max hJ (by simpa using he) hb'
        rw [hp] at hp'
        cases Option.some.inj hp'
        exact ⟨by simp, by simpa [entry] using hmax⟩
      | succ i =>
        have hne : J ≠ I := by
          intro hji
          have hIe := (pick_spec hp).1
          rw [hji] at he
          push_cast at he
          omega
        have hJ' : J ∈ a.erase I := (Multiset.mem_erase_of_ne hne).mpr hJ
        have hi' : i ≤ (chain (a.erase I) (e - 1) I.beginning).1.length := by
          simpa using hi
        have he' : J.ending = e - 1 - (i : ℤ) := by push_cast at he; omega
        have hb' : J.beginning < if i = 0 then I.beginning else
            (entry (chain (a.erase I) (e - 1) I.beginning).1 (i - 1)).beginning := by
          cases i <;> simpa [entry] using hb
        have hh := ih (a.erase I) (Multiset.card_erase_lt_of_mem (pick_mem hp))
          (e - 1) I.beginning i hi' hJ' he' hb'
        simpa [entry] using hh

private theorem round_first_max {a : Multisegment} {r : Round} (hr : round a = some r)
    {J : Interval} (hJ : J ∈ a) : J ≤ r.first := by
  unfold round at hr
  cases hs : a.sort (fun I J => J ≤ I) with
  | nil => simp [hs] at hr
  | cons I l =>
    simp only [hs, Option.some.injEq] at hr
    subst r
    exact sorted_head_max hs hJ

private theorem round_greedy {a : Multisegment} {r : Round} (hr : round a = some r)
    (i : ℕ) (hi : i ≤ r.selectedList.length) {J : Interval}
    (hJ : J ∈ a) (he : J.ending = r.first.ending - (i : ℤ))
    (hb : i ≠ 0 → J.beginning < (entry r.selectedList (i - 1)).beginning) :
    i < r.selectedList.length ∧ J.beginning ≤ (entry r.selectedList i).beginning := by
  unfold round at hr
  cases hs : a.sort (fun I J => J ≤ I) with
  | nil => simp [hs] at hr
  | cons I l =>
    simp only [hs, Option.some.injEq] at hr
    subst r
    have ha : I ::ₘ (l : Multisegment) = a := by
      have hh := Multiset.sort_eq a (fun I J => J ≤ I)
      simpa [hs] using hh
    cases i with
    | zero =>
      exact ⟨by simp [Round.selectedList], by
        simpa [Round.selectedList, entry] using
          order_beginning (sorted_head_max hs hJ) (by simpa using he)⟩
    | succ i =>
      have hne : J ≠ I := by intro hh; rw [hh] at he; dsimp at he; omega
      have hm : J ∈ (l : Multisegment) := by
        rw [← ha] at hJ
        exact (Multiset.mem_cons.mp hJ).resolve_left hne
      have hi' : i ≤ (chain (l : Multisegment) (I.ending - 1) I.beginning).1.length := by
        simpa [Round.selectedList] using hi
      have he' : J.ending = I.ending - 1 - (i : ℤ) := by dsimp at he; omega
      have hb' : J.beginning < if i = 0 then I.beginning else
          (entry (chain (l : Multisegment) (I.ending - 1) I.beginning).1 (i - 1)).beginning := by
        have hh := hb (Nat.succ_ne_zero i)
        cases i <;> simpa [Round.selectedList, entry] using hh
      have hh := chain_greedy (l : Multisegment) (I.ending - 1) I.beginning i hi' hm he' hb'
      simpa [Round.selectedList, entry] using hh

private theorem selected_mem {a : Multisegment} {r : Round} (hr : round a = some r)
    {I : Interval} (hI : I ∈ r.selectedList) : I ∈ a := by
  rw [← round_partition hr]
  exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_coe.mpr hI))

private theorem residual_mem {r : Round} {I : Interval} (hI : I ∈ r.residual) :
    I ∈ r.untouched ∨ ∃ K ∈ r.selectedList,
      I.beginning = K.beginning ∧ I.ending = K.ending - 1 := by
  rcases Multiset.mem_add.mp hI with ht | hs
  · exact Or.inl ht
  · right
    obtain ⟨K, hK, hIK⟩ := Multiset.mem_bind.mp hs
    refine ⟨K, Multiset.mem_coe.mp hK, ?_⟩
    unfold Interval.dropLast at hIK
    split_ifs at hIK with hk
    · simp only [Multiset.mem_singleton] at hIK
      subst I
      exact ⟨rfl, rfl⟩
    · simp at hIK

private theorem round_entry_ending {a : Multisegment} {r : Round} (hr : round a = some r)
    (i : ℕ) (hi : i < r.selectedList.length) :
    (entry r.selectedList i).ending = r.first.ending - (i : ℤ) := by
  rw [entry_eq _ _ hi]
  exact round_ending hr i hi

private theorem round_entry_decreasing {a : Multisegment} {r : Round} (hr : round a = some r)
    (i : ℕ) (hi : i + 1 < r.selectedList.length) :
    (entry r.selectedList (i + 1)).beginning < (entry r.selectedList i).beginning := by
  rw [entry_eq _ _ hi, entry_eq _ _ (by omega)]
  exact (List.pairwise_iff_getElem.mp (round_decreasing hr)) i (i + 1) (by omega) hi (by omega)

private theorem untouched_mem {a : Multisegment} {r : Round} (hr : round a = some r)
    {I : Interval} (hI : I ∈ r.untouched) : I ∈ a := by
  rw [← round_partition hr]
  exact Multiset.mem_add.mpr (Or.inr hI)

/-- The greedy chain lengths cannot increase between consecutive rounds
whose greatest ending is unchanged. -/
private theorem round_length_mono {a : Multisegment} {r r' : Round}
    (hr : round a = some r) (hr' : round r.residual = some r')
    (heq : r'.first.ending = r.first.ending) :
    r'.selectedList.length ≤ r.selectedList.length := by
  have hdom : ∀ i, i < r'.selectedList.length →
      i < r.selectedList.length ∧
      (entry r'.selectedList i).beginning ≤ (entry r.selectedList i).beginning := by
    intro i
    induction i with
    | zero =>
      intro hi
      have hm := selected_mem hr' (entry_mem _ 0 hi)
      have he := round_entry_ending hr' 0 hi
      rw [heq] at he
      rcases residual_mem hm with hu | ⟨K, hK, _, hKe⟩
      · exact round_greedy hr 0 (by omega) (untouched_mem hr hu) he (by simp)
      · have hmax := order_ending (round_first_max hr (selected_mem hr hK))
        omega
    | succ i ih =>
      intro hi
      have hiprev : i < r'.selectedList.length := by omega
      obtain ⟨hiold, hprev⟩ := ih hiprev
      have hstep := round_entry_decreasing hr' i hi
      have hm := selected_mem hr' (entry_mem _ (i + 1) hi)
      have he := round_entry_ending hr' (i + 1) hi
      rw [heq] at he
      rcases residual_mem hm with hu | ⟨K, hK, hKb, hKe⟩
      · apply round_greedy hr (i + 1) (by omega) (untouched_mem hr hu) he
        intro _
        simpa using lt_of_lt_of_le hstep hprev
      · obtain ⟨j, hj, hKj⟩ := List.mem_iff_getElem.mp hK
        have hje := round_ending hr j hj
        rw [hKj] at hje
        have hji : j = i := by push_cast at he; omega
        subst j
        have hentry := entry_eq r.selectedList i hj
        rw [hKj] at hentry
        rw [hentry] at hprev
        omega
  by_contra hlen
  have hi : r.selectedList.length < r'.selectedList.length := by omega
  have hh := (hdom r.selectedList.length hi).1
  omega

private theorem emitted_length (r : Round) : r.emitted.length = r.selectedList.length := by
  have hh : r.first.ending - (r.first.ending - (r.tail.length : ℤ)) = (r.tail.length : ℤ) := by ring
  simp [Round.emitted, Interval.length, hh, Round.selectedList]

private theorem round_length_lower {a : Multisegment} {r : Round} (hr : round a = some r)
    {b : ℤ} (hb : ∀ I ∈ a, b ≤ I.ending) :
    (r.selectedList.length : ℤ) ≤ r.first.ending - b + 1 := by
  have hlen : 0 < r.selectedList.length := by simp [Round.selectedList]
  have hi : r.selectedList.length - 1 < r.selectedList.length := by omega
  have hm := selected_mem hr (entry_mem _ _ hi)
  have he := round_entry_ending hr _ hi
  have hh := hb _ hm
  have hn : ((r.selectedList.length - 1 : ℕ) : ℤ) = (r.selectedList.length : ℤ) - 1 := by omega
  omega

private theorem residual_ending_bounds {a : Multisegment} {r : Round} (hr : round a = some r)
    (k : ℕ) (hb : ∀ I ∈ a, r.first.ending - (k : ℤ) ≤ I.ending)
    (hlen : r.selectedList.length ≤ k) :
    ∀ I ∈ r.residual,
      r.first.ending - (k : ℤ) ≤ I.ending ∧ I.ending ≤ r.first.ending := by
  intro I hI
  rcases residual_mem hI with hu | ⟨K, hK, _, hKe⟩
  · have hm := untouched_mem hr hu
    exact ⟨hb I hm, order_ending (round_first_max hr hm)⟩
  · obtain ⟨j, hj, hKj⟩ := List.mem_iff_getElem.mp hK
    have he := round_ending hr j hj
    rw [hKj] at he
    constructor <;> omega

/-- A lower envelope one step below the longest allowed selection is stable
through a phase with fixed greatest ending, and resets when that ending drops. -/
private theorem dual_bound_of_round (a : Multisegment) :
    ∀ (r : Round), round a = some r → ∀ (k : ℕ),
      (∀ I ∈ a, r.first.ending - (k : ℤ) ≤ I.ending) →
      r.selectedList.length ≤ k → ∀ J ∈ dual a, J.length ≤ k := by
  induction a using (measure (fun a : Multisegment => weight a)).wf.induction with
  | h a ih =>
    intro r hr k hb hlen J hJ
    rw [dual_of_round hr] at hJ
    rcases Multiset.mem_cons.mp hJ with rfl | hJ
    · rw [emitted_length]
      exact hlen
    · cases hr' : round r.residual with
      | none =>
        have hz := (round_none_iff r.residual).mp hr'
        rw [hz, dual_zero] at hJ
        simp at hJ
      | some r' =>
        have hbounds := residual_ending_bounds hr k hb hlen
        have hfirst : r'.first ∈ r.residual :=
          selected_mem hr' (by simp [Round.selectedList])
        have htop := (hbounds _ hfirst).2
        have hlen' : r'.selectedList.length ≤ k := by
          by_cases he : r'.first.ending = r.first.ending
          · exact (round_length_mono hr hr' he).trans hlen
          · have hh := round_length_lower hr' (fun I hI => (hbounds I hI).1)
            omega
        have hb' : ∀ I ∈ r.residual, r'.first.ending - (k : ℤ) ≤ I.ending := by
          intro I hI
          have hh := (hbounds I hI).1
          omega
        exact ih r.residual (round_weight_lt hr) r' hr' k hb' hlen' J hJ

/-- Badulescu property (P) for the actual total MW recursion, including the
empty input and a half-open range with zero possible endings. -/
theorem endingBound : EndingBound := by
  intro a b k hb J hJ
  cases hr : round a with
  | none =>
    have hz := (round_none_iff a).mp hr
    rw [hz, dual_zero] at hJ
    simp at hJ
  | some r =>
    have hfirst : r.first ∈ a := selected_mem hr (by simp [Round.selectedList])
    have htop := (hb _ hfirst).2
    have hlo : ∀ I ∈ a, r.first.ending - (k : ℤ) ≤ I.ending := by
      intro I hI
      have hh := (hb I hI).1
      omega
    have hlen : r.selectedList.length ≤ k := by
      have hh := round_length_lower hr (fun I hI => (hb I hI).1)
      omega
    exact dual_bound_of_round a r hr k hlo hlen J hJ

end Langlands.MoeglinWaldspurger
