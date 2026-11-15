import Langlands.Representation.Classification.MoeglinWaldspurgerDerivationCombinatorics

/-!
# The chain compatibility of the bottom-up matching

Proof of `ChainUnmatchedCompatibility`.
-/

namespace Langlands.MoeglinWaldspurger.Derivation

open Langlands.MoeglinWaldspurger

/-! ### Scanning concatenated lists -/

/-- The pool left after scanning a list. -/
def scanPool (x : ℤ) : List Interval → ℕ → ℕ
  | [], pool => pool
  | I :: l, pool =>
    if I.ending = x - 1 then scanPool x l (pool + 1)
    else if I.ending = x then
      if pool = 0 then scanPool x l pool else scanPool x l (pool - 1)
    else scanPool x l pool

theorem unmatchedScan_append (x : ℤ) :
    ∀ (l₁ l₂ : List Interval) (pool : ℕ),
      unmatchedScan x (l₁ ++ l₂) pool =
        unmatchedScan x l₁ pool ++ unmatchedScan x l₂ (scanPool x l₁ pool)
  | [], _, _ => rfl
  | I :: l₁, l₂, pool => by
    simp only [List.cons_append, unmatchedScan, scanPool]
    split_ifs <;> simp [unmatchedScan_append x l₁ l₂]

theorem scanPool_append (x : ℤ) :
    ∀ (l₁ l₂ : List Interval) (pool : ℕ),
      scanPool x (l₁ ++ l₂) pool = scanPool x l₂ (scanPool x l₁ pool)
  | [], _, _ => rfl
  | I :: l₁, l₂, pool => by
    simp only [List.cons_append, scanPool]
    split_ifs <;> simp [scanPool_append x l₁ l₂]

theorem unmatchedScan_of_ending_eq (x : ℤ) :
    ∀ (l : List Interval), (∀ I ∈ l, I.ending = x) →
      unmatchedScan x l 0 = l ∧ scanPool x l 0 = 0
  | [], _ => ⟨rfl, rfl⟩
  | I :: l, h => by
    have hI : I.ending = x := h I (List.mem_cons_self ..)
    have ih := unmatchedScan_of_ending_eq x l (fun J hJ => h J (List.mem_cons_of_mem _ hJ))
    simp only [unmatchedScan, scanPool, hI, show ¬ x = x - 1 by omega, ↓reduceIte, ih,
      and_self]

theorem unmatchedScan_of_ending_eq_sub_one (x : ℤ) :
    ∀ (l : List Interval) (pool : ℕ), (∀ I ∈ l, I.ending = x - 1) →
      unmatchedScan x l pool = [] ∧ scanPool x l pool = pool + l.length
  | [], _, _ => ⟨rfl, rfl⟩
  | I :: l, pool, h => by
    have hI : I.ending = x - 1 := h I (List.mem_cons_self ..)
    have ih := unmatchedScan_of_ending_eq_sub_one x l (pool + 1)
      (fun J hJ => h J (List.mem_cons_of_mem _ hJ))
    simp only [unmatchedScan, scanPool, hI, ↓reduceIte, ih, List.length_cons, true_and]
    omega

theorem unmatchedScan_of_ending_ne (x : ℤ) :
    ∀ (l : List Interval) (pool : ℕ), (∀ I ∈ l, I.ending ≠ x) → unmatchedScan x l pool = []
  | [], _, _ => rfl
  | I :: l, pool, h => by
    have hI : I.ending ≠ x := h I (List.mem_cons_self ..)
    have ih := fun p => unmatchedScan_of_ending_ne x l p
      (fun J hJ => h J (List.mem_cons_of_mem _ hJ))
    simp only [unmatchedScan, hI, ↓reduceIte, ih]
    split_ifs <;> rfl

/-! ### Sorting a sum of ordered blocks -/

theorem sort_add_of_scanLE (m₁ m₂ : Multiset Interval)
    (h : ∀ I ∈ m₁, ∀ J ∈ m₂, ScanLE I J) :
    (m₁ + m₂).sort ScanLE = m₁.sort ScanLE ++ m₂.sort ScanLE := by
  apply List.Perm.eq_of_pairwise' (r := ScanLE)
  · exact Multiset.pairwise_sort _ _
  · rw [List.pairwise_append]
    refine ⟨Multiset.pairwise_sort _ _, Multiset.pairwise_sort _ _, ?_⟩
    intro I hI J hJ
    exact h I ((Multiset.mem_sort _).mp hI) J ((Multiset.mem_sort _).mp hJ)
  · rw [← Multiset.coe_eq_coe, Multiset.sort_eq, ← Multiset.coe_add, Multiset.sort_eq,
      Multiset.sort_eq]

/-- Unmatched occurrences of three consecutive blocks in the scan order. -/
theorem unmatched_three_blocks (x : ℤ) (m₁ m₂ m₃ : Multisegment)
    (h₁₂ : ∀ I ∈ m₁, ∀ J ∈ m₂, ScanLE I J) (h₁₃ : ∀ I ∈ m₁ + m₂, ∀ J ∈ m₃, ScanLE I J) :
    unmatched (m₁ + m₂ + m₃) x =
      ((unmatchedScan x (m₁.sort ScanLE) 0 ++ unmatchedScan x (m₂.sort ScanLE)
        (scanPool x (m₁.sort ScanLE) 0) ++ unmatchedScan x (m₃.sort ScanLE)
          (scanPool x (m₂.sort ScanLE) (scanPool x (m₁.sort ScanLE) 0)) : List Interval) :
        Multiset Interval) := by
  unfold unmatched
  rw [sort_add_of_scanLE _ _ h₁₃, sort_add_of_scanLE _ _ h₁₂, unmatchedScan_append,
    unmatchedScan_append, scanPool_append]

/-! ### Removing the last chain element from the matching -/

theorem mem_dropLast {I J : Interval} (h : J ∈ I.dropLast) :
    J.beginning = I.beginning ∧ J.ending = I.ending - 1 := by
  unfold Interval.dropLast at h
  split_ifs at h
  · rw [Multiset.mem_singleton] at h
    subst h
    exact ⟨rfl, rfl⟩
  · simp at h

theorem dropLast_of_lt {I : Interval} (h : I.beginning < I.ending) :
    I.dropLast = {⟨I.beginning, I.ending - 1, by omega⟩} := by
  simp only [Interval.dropLast, h, ↓reduceDIte]

/-- **Scan lemma.** Let `Δ` end at `c` with beginning `β`, let no occurrence ending at `c - 1`
begin before `β`, and let no occurrence ending at `c` begin strictly between `β` and `γ`.
Then all occurrences ending at `c` and beginning at most at `β` are unmatched, and after
replacing `Δ` by its shortening and adding `[γ, c]` (when `γ ≤ c`; nothing is added when no
occurrence ending at `c` begins at `γ` or later), the unmatched occurrences lose exactly
one copy of `Δ`. -/
theorem unmatched_erase_last {b : Multisegment} {c γ : ℤ} {Δ : Interval} {E : Multisegment}
    (hΔ : Δ ∈ b) (hΔc : Δ.ending = c) (hβγ : Δ.beginning < γ)
    (h1 : ∀ I ∈ b, I.ending = c - 1 → Δ.beginning ≤ I.beginning)
    (h2 : ∀ I ∈ b, I.ending = c → I.beginning ≤ Δ.beginning ∨ γ ≤ I.beginning)
    (hE : (∃ hγ : γ ≤ c, E = {⟨γ, c, hγ⟩}) ∨
      (E = 0 ∧ ∀ I ∈ b, I.ending = c → I.beginning ≤ Δ.beginning)) :
    b.filter (fun I => I.ending = c ∧ I.beginning ≤ Δ.beginning) ≤ unmatched b c ∧
      unmatched (b.erase Δ + Δ.dropLast + E) c = (unmatched b c).erase Δ := by
  generalize hβ : Δ.beginning = β at h1 h2 hE hβγ ⊢
  obtain ⟨P, hP⟩ : ∃ P, P = b.filter (fun I => I.ending = c ∧ I.beginning ≤ β) := ⟨_, rfl⟩
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q, Q = b.filter (fun I => I.ending = c - 1 ∧ I.beginning < γ) :=
    ⟨_, rfl⟩
  obtain ⟨Q₂, hQ₂⟩ : ∃ Q, Q = b.filter (fun I => TwoEnd c I ∧ γ ≤ I.beginning) := ⟨_, rfl⟩
  rw [← hP]
  have hmemP : ∀ I ∈ P, I.ending = c ∧ I.beginning ≤ β := by
    intro I hI; rw [hP] at hI; exact (Multiset.mem_filter.mp hI).2
  have hmemQ₁ : ∀ I ∈ Q₁, I.ending = c - 1 ∧ I.beginning < γ := by
    intro I hI; rw [hQ₁] at hI; exact (Multiset.mem_filter.mp hI).2
  have hmemQ₂ : ∀ I ∈ Q₂, TwoEnd c I ∧ γ ≤ I.beginning := by
    intro I hI; rw [hQ₂] at hI; exact (Multiset.mem_filter.mp hI).2
  have hQ₁b : ∀ I ∈ Q₁, I ∈ b := by
    intro I hI; rw [hQ₁] at hI; exact (Multiset.mem_filter.mp hI).1
  have hQ₂b : ∀ I ∈ Q₂, I ∈ b := by
    intro I hI; rw [hQ₂] at hI; exact (Multiset.mem_filter.mp hI).1
  have hΔP : Δ ∈ P := by
    rw [hP]; exact Multiset.mem_filter.mpr ⟨hΔ, hΔc, hβ.le⟩
  have hJ : b.filter (TwoEnd c) = P + Q₁ + Q₂ := by
    ext I
    rw [hP, hQ₁, hQ₂]
    simp only [Multiset.count_add, Multiset.count_filter]
    unfold TwoEnd
    by_cases hI : I ∈ b
    · have k1 := h1 I hI
      have k2 := h2 I hI
      by_cases e1 : I.ending = c
      · by_cases e3 : I.beginning ≤ β
        · have e4 : ¬ γ ≤ I.beginning := by omega
          simp [e1, e3, e4, show c ≠ c - 1 by omega]
        · have e4 : γ ≤ I.beginning := by omega
          simp [e1, e3, e4]
      · by_cases e2 : I.ending = c - 1
        · by_cases e4 : γ ≤ I.beginning
          · simp [e2, e4]
          · simp [e2, e4, show I.beginning < γ by omega]
        · simp [e1, e2]
    · simp [Multiset.count_eq_zero.mpr hI]
  -- the original order
  have o₁₂ : ∀ I ∈ P, ∀ J ∈ Q₁, ScanLE I J := by
    intro I hI J hJ
    obtain ⟨hIe, hIb⟩ := hmemP I hI
    obtain ⟨hJe, -⟩ := hmemQ₁ J hJ
    have := h1 J (hQ₁b J hJ) hJe
    unfold ScanLE
    omega
  have o₁₃ : ∀ I ∈ P + Q₁, ∀ J ∈ Q₂, ScanLE I J := by
    intro I hI J hJ
    obtain ⟨-, hJb⟩ := hmemQ₂ J hJ
    have : I.beginning < γ := by
      rcases Multiset.mem_add.mp hI with hI | hI
      · have := (hmemP I hI).2; omega
      · exact (hmemQ₁ I hI).2
    unfold ScanLE
    omega
  have hPscan := unmatchedScan_of_ending_eq c (P.sort ScanLE)
    (fun I hI => (hmemP I ((Multiset.mem_sort _).mp hI)).1)
  have hQ₁scan := unmatchedScan_of_ending_eq_sub_one c (Q₁.sort ScanLE) 0
    (fun I hI => (hmemQ₁ I ((Multiset.mem_sort _).mp hI)).1)
  set R := unmatchedScan c (Q₂.sort ScanLE) (Multiset.card Q₁) with hR
  have hU : unmatched b c = P + (R : Multiset Interval) := by
    rw [← unmatched_filter, hJ, unmatched_three_blocks c P Q₁ Q₂ o₁₂ o₁₃, hPscan.1, hPscan.2,
      hQ₁scan.1, hQ₁scan.2, List.append_nil, ← Multiset.coe_add, Multiset.sort_eq,
      Multiset.length_sort, zero_add]
  -- the modified multiset
  have hdl : ∀ I ∈ Δ.dropLast, I.ending = c - 1 ∧ I.beginning = β := by
    intro I hI
    obtain ⟨h₁, h₂⟩ := mem_dropLast hI
    exact ⟨by omega, h₁.trans hβ⟩
  have hEmem : ∀ I ∈ E, I.ending = c ∧ I.beginning = γ := by
    intro I hI
    rcases hE with ⟨hγ, rfl⟩ | ⟨rfl, -⟩
    · rw [Multiset.mem_singleton] at hI; subst hI; exact ⟨rfl, rfl⟩
    · simp at hI
  have hJ' : (b.erase Δ + Δ.dropLast + E).filter (TwoEnd c) =
      P.erase Δ + (Δ.dropLast + Q₁) + (E + Q₂) := by
    rw [Multiset.filter_add, Multiset.filter_add]
    have e1 : (b.erase Δ).filter (TwoEnd c) = (b.filter (TwoEnd c)).erase Δ := by
      conv_rhs => rw [← Multiset.cons_erase hΔ]
      rw [Multiset.filter_cons_of_pos (p := TwoEnd c) _ (show TwoEnd c Δ from Or.inl hΔc),
        Multiset.erase_cons_head]
    have e2 : Δ.dropLast.filter (TwoEnd c) = Δ.dropLast :=
      Multiset.filter_eq_self.mpr fun I hI => Or.inr (hdl I hI).1
    have e3 : E.filter (TwoEnd c) = E :=
      Multiset.filter_eq_self.mpr fun I hI => Or.inl (hEmem I hI).1
    rw [e1, e2, e3, hJ, Multiset.erase_add_left_pos _ (Multiset.mem_add.mpr (Or.inl hΔP)),
      Multiset.erase_add_left_pos _ hΔP]
    abel
  have hPe : ∀ I ∈ P.erase Δ, I.ending = c ∧ I.beginning ≤ β := fun I hI =>
    hmemP I (Multiset.mem_of_mem_erase hI)
  have o'₁₂ : ∀ I ∈ P.erase Δ, ∀ J ∈ Δ.dropLast + Q₁, ScanLE I J := by
    intro I hI J hJ
    obtain ⟨hIe, hIb⟩ := hPe I hI
    have : J.ending = c - 1 ∧ β ≤ J.beginning := by
      rcases Multiset.mem_add.mp hJ with hJ | hJ
      · have := hdl J hJ; omega
      · have hJe := (hmemQ₁ J hJ).1
        exact ⟨hJe, h1 J (hQ₁b J hJ) hJe⟩
    unfold ScanLE
    omega
  have o'₁₃ : ∀ I ∈ P.erase Δ + (Δ.dropLast + Q₁), ∀ J ∈ E + Q₂, ScanLE I J := by
    intro I hI J hJ
    have hIb : I.beginning < γ := by
      rcases Multiset.mem_add.mp hI with hI | hI
      · have := (hPe I hI).2; omega
      · rcases Multiset.mem_add.mp hI with hI | hI
        · have := (hdl I hI).2; omega
        · exact (hmemQ₁ I hI).2
    have hJb : γ ≤ J.beginning := by
      rcases Multiset.mem_add.mp hJ with hJ | hJ
      · exact (hEmem J hJ).2.ge
      · exact (hmemQ₂ J hJ).2
    unfold ScanLE
    omega
  have hP'scan := unmatchedScan_of_ending_eq c ((P.erase Δ).sort ScanLE)
    (fun I hI => (hPe I ((Multiset.mem_sort _).mp hI)).1)
  have hQ'scan := unmatchedScan_of_ending_eq_sub_one c ((Δ.dropLast + Q₁).sort ScanLE) 0
    (fun I hI => by
      rcases Multiset.mem_add.mp ((Multiset.mem_sort _).mp hI) with hI | hI
      · exact (hdl I hI).1
      · exact (hmemQ₁ I hI).1)
  have hR' : unmatchedScan c ((E + Q₂).sort ScanLE) (Multiset.card (Δ.dropLast + Q₁)) = R := by
    rcases hE with ⟨hγ, rfl⟩ | ⟨rfl, hall⟩
    · have hlt : Δ.beginning < Δ.ending := by omega
      rw [dropLast_of_lt hlt, Multiset.card_add, Multiset.card_singleton,
        Multiset.singleton_add, Multiset.sort_cons]
      · simp only [unmatchedScan, show ¬ c = c - 1 by omega, ↓reduceIte,
          show ¬ 1 + Multiset.card Q₁ = 0 by omega]
        rw [hR]
        congr 1
        omega
      · intro J hJ
        obtain ⟨hJt, hJb⟩ := hmemQ₂ J hJ
        unfold TwoEnd at hJt
        show γ < J.beginning ∨ (γ = J.beginning ∧ J.ending ≤ c)
        omega
    · have hQ₂ne : ∀ I ∈ Q₂, I.ending ≠ c := by
        intro I hI hIe
        obtain ⟨-, hIb⟩ := hmemQ₂ I hI
        have := hall I (hQ₂b I hI) hIe
        omega
      rw [zero_add, hR, unmatchedScan_of_ending_ne c _ _
          (fun I hI => hQ₂ne I ((Multiset.mem_sort _).mp hI)),
        unmatchedScan_of_ending_ne c _ _
          (fun I hI => hQ₂ne I ((Multiset.mem_sort _).mp hI))]
  have hU' : unmatched (b.erase Δ + Δ.dropLast + E) c = P.erase Δ + (R : Multiset Interval) := by
    rw [← unmatched_filter, hJ', unmatched_three_blocks c _ _ _ o'₁₂ o'₁₃, hP'scan.1,
      hP'scan.2, hQ'scan.1, hQ'scan.2, List.append_nil, ← Multiset.coe_add, Multiset.sort_eq,
      Multiset.length_sort, zero_add, hR']
  refine ⟨?_, ?_⟩
  · rw [hU]
    exact Multiset.le_add_right _ _
  · rw [hU', hU, Multiset.erase_add_left_pos _ hΔP]

/-! ### Chains -/

theorem chain_of_pick_some {a : Multisegment} {e b : ℤ} {I : Interval}
    (hp : pick a e b = some I) :
    chain a e b = (I :: (chain (a.erase I) (e - 1) I.beginning).1,
      (chain (a.erase I) (e - 1) I.beginning).2) := by
  rw [chain]
  split
  · rename_i h; rw [hp] at h; cases h
  · rename_i J h; rw [hp] at h; cases h; rfl

theorem chain_mem_ending_le (m : Multisegment) (e b : ℤ) {J : Interval}
    (hJ : J ∈ (chain m e b).1) : J.ending ≤ e := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hJ
  rw [chain_ending m e b i hi]
  omega

/-- The last selection of a nonempty chain: its maximality among the candidates and the
reason the chain stops after it. -/
theorem chain_last : ∀ (m : Multisegment) (e b : ℤ), (chain m e b).1 ≠ [] →
    ∃ (L₀ : List Interval) (Δ : Interval), (chain m e b).1 = L₀ ++ [Δ] ∧ Δ ∈ m ∧
      Δ.ending = e - L₀.length ∧ Δ.beginning < (L₀.map Interval.beginning).getLastD b ∧
      (∀ I ∈ m, I.ending = Δ.ending → I.beginning < (L₀.map Interval.beginning).getLastD b →
        I.beginning ≤ Δ.beginning) ∧
      (∀ I ∈ m, I.ending = Δ.ending - 1 → Δ.beginning ≤ I.beginning) ∧
      (∀ K ∈ L₀, Δ.ending < K.ending) ∧
      (L₀ = [] ∨ ∃ L₁ Δ', L₀ = L₁ ++ [Δ'] ∧ Δ'.ending = Δ.ending + 1 ∧
        ∀ K ∈ L₁, Δ.ending + 1 < K.ending) := by
  intro m
  induction m using (measure (fun a : Multisegment => Multiset.card a)).wf.induction with
  | h m ih =>
  intro e b hne
  rcases hp : pick m e b with _ | I
  · rw [chain_of_pick_none hp] at hne; exact absurd rfl hne
  obtain ⟨hIe, hIb⟩ := pick_spec hp
  have hIm := pick_mem hp
  rw [chain_of_pick_some hp]
  dsimp only
  by_cases hnil : (chain (m.erase I) (e - 1) I.beginning).1 = []
  · refine ⟨[], I, by rw [hnil]; rfl, hIm, by simpa using hIe, by simpa using hIb, ?_, ?_,
      by simp, Or.inl rfl⟩
    · intro J hJ hJe hJb
      exact Langlands.MoeglinWaldspurger.Involution.pick_maximal hp hJ (hJe.trans hIe) (by simpa using hJb)
    · intro J hJ hJe
      have hpn := (chain_eq_nil_iff _ _ _).mp hnil
      have hJ' : J ∈ m.erase I := (Multiset.mem_erase_of_ne (by rintro rfl; omega)).mpr hJ
      rcases (Langlands.MoeglinWaldspurger.Involution.pick_none_iff _ _ _).mp hpn J hJ' with h | h
      · omega
      · exact h
  · obtain ⟨L₀, Δ, hL, hΔm, hΔe, hΔb, hmax, hstop, hhigh, hprev⟩ :=
      ih (m.erase I) (Multiset.card_erase_lt_of_mem hIm) (e - 1) I.beginning hnil
    have hgl : ((I :: L₀).map Interval.beginning).getLastD b =
        (L₀.map Interval.beginning).getLastD I.beginning := by
      rw [List.map_cons, List.getLastD_cons]
    refine ⟨I :: L₀, Δ, by rw [hL]; rfl, Multiset.mem_of_mem_erase hΔm, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_cons]; push_cast; omega
    · rw [hgl]; exact hΔb
    · intro J hJ hJe hJb
      rw [hgl] at hJb
      have hJ' : J ∈ m.erase I := (Multiset.mem_erase_of_ne (by rintro rfl; omega)).mpr hJ
      exact hmax J hJ' hJe hJb
    · intro J hJ hJe
      have hJ' : J ∈ m.erase I := (Multiset.mem_erase_of_ne (by rintro rfl; omega)).mpr hJ
      exact hstop J hJ' hJe
    · intro K hK
      rcases List.mem_cons.mp hK with rfl | hK
      · omega
      · exact hhigh K hK
    · right
      rcases hprev with rfl | ⟨L₁, Δ', rfl, hΔ'e, hL₁⟩
      · exact ⟨[], I, rfl, by simp at hΔe; omega, by simp⟩
      · refine ⟨I :: L₁, Δ', rfl, hΔ'e, ?_⟩
        intro K hK
        rcases List.mem_cons.mp hK with rfl | hK
        · simp at hΔe; omega
        · exact hL₁ K hK

theorem filter_erase_of_pos {s : Multisegment} (p : Interval → Prop) [DecidablePred p]
    {x : Interval} (hx : p x) : (s.erase x).filter p = (s.filter p).erase x := by
  ext J
  by_cases hJ : J = x
  · subst hJ; simp [Multiset.count_erase_self, hx]
  · simp [Multiset.count_erase_of_ne hJ, Multiset.count_filter]

/-- Discarding the occurrences ending at most at `k` truncates the chain. -/
theorem chain_filter_gt (k : ℤ) : ∀ (m : Multisegment) (e b : ℤ),
    chain (m.filter (fun I => k < I.ending)) e b =
      ((chain m e b).1.filter (fun I => decide (k < I.ending)),
        (chain m e b).2.filter (fun I => k < I.ending)) := by
  intro m
  induction m using (measure (fun a : Multisegment => Multiset.card a)).wf.induction with
  | h m ih =>
  intro e b
  by_cases hek : e ≤ k
  · have hpn : pick (m.filter (fun I => k < I.ending)) e b = none := by
      rw [Langlands.MoeglinWaldspurger.Involution.pick_none_iff]
      intro I hI
      left
      have := (Multiset.mem_filter.mp hI).2
      omega
    rw [chain_of_pick_none hpn]
    have hL : (chain m e b).1.filter (fun I => decide (k < I.ending)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro I hI
      have := chain_mem_ending_le m e b hI
      simp only [decide_eq_true_eq]
      omega
    rw [hL]
    have hp := chain_partition m e b
    conv_lhs => rw [← hp]
    rw [Multiset.filter_add, Multiset.filter_coe, hL]
    simp
  · have hek : k < e := by omega
    have hff : (m.filter (fun I => k < I.ending)).filter
        (fun I => I.ending = e ∧ I.beginning < b) =
        m.filter (fun I => I.ending = e ∧ I.beginning < b) := by
      rw [Multiset.filter_filter]
      apply Multiset.filter_congr
      intro I _
      constructor
      · rintro ⟨h, -⟩; exact h
      · intro h; exact ⟨h, by have := h.1; omega⟩
    have hpick : pick (m.filter (fun I => k < I.ending)) e b = pick m e b := by
      unfold pick
      rw [hff]
    rcases hp : pick m e b with _ | I
    · rw [hp] at hpick
      rw [chain_of_pick_none hpick, chain_of_pick_none hp]
      simp
    · rw [hp] at hpick
      obtain ⟨hIe, -⟩ := pick_spec hp
      have hIm := pick_mem hp
      rw [chain_of_pick_some hpick, chain_of_pick_some hp,
        ← filter_erase_of_pos (fun I => k < I.ending) (by omega : k < I.ending),
        ih (m.erase I) (Multiset.card_erase_lt_of_mem hIm) (e - 1) I.beginning]
      simp only [List.filter_cons, decide_eq_true_eq, show k < I.ending by omega, ↓reduceIte]

/-- Adding occurrences that do not interfere with a chain leaves its selections unchanged. -/
theorem chain_add_low (w : Multisegment) : ∀ (h : Multisegment) (e b : ℤ),
    (∀ I ∈ w, I.ending < e - (chain h e b).1.length ∨
      (I.ending = e - (chain h e b).1.length ∧
        ((chain h e b).1.map Interval.beginning).getLastD b ≤ I.beginning)) →
    chain (h + w) e b = ((chain h e b).1, (chain h e b).2 + w) := by
  intro h
  induction h using (measure (fun a : Multisegment => Multiset.card a)).wf.induction with
  | h h ih =>
  intro e b hw
  rcases hp : pick h e b with _ | I
  · rw [chain_of_pick_none hp] at hw ⊢
    have hpn : pick (h + w) e b = none := by
      rw [Langlands.MoeglinWaldspurger.Involution.pick_none_iff] at hp ⊢
      intro J hJ
      rcases Multiset.mem_add.mp hJ with hJ | hJ
      · exact hp J hJ
      · rcases hw J hJ with h' | ⟨-, h''⟩
        · left; simp at h'; omega
        · right; simpa using h''
    rw [chain_of_pick_none hpn]
  · have hIm := pick_mem hp
    rw [chain_of_pick_some hp] at hw ⊢
    have hw' : ∀ J ∈ w, J.ending < e := by
      intro J hJ
      rcases hw J hJ with h' | ⟨h', -⟩ <;> simp at h' <;> omega
    have hpick : pick (h + w) e b = some I := by
      rw [← hp]
      unfold pick
      have hw0 : w.filter (fun J => J.ending = e ∧ J.beginning < b) = 0 :=
        Multiset.filter_eq_nil.mpr (fun J hJ hq => by have := hw' J hJ; have := hq.1; omega)
      rw [Multiset.filter_add, hw0, add_zero]
    rw [chain_of_pick_some hpick, Multiset.erase_add_left_pos _ hIm,
      ih (h.erase I) (Multiset.card_erase_lt_of_mem hIm) (e - 1) I.beginning]
    intro J hJ
    rcases hw J hJ with h' | ⟨h', h''⟩
    · left; simp only [List.length_cons] at h'; push_cast at h'; omega
    · right
      refine ⟨by simp only [List.length_cons] at h'; push_cast at h'; omega, ?_⟩
      rw [List.map_cons, List.getLastD_cons] at h''
      exact h''

theorem round_eq_of_max {a : Multisegment} {I : Interval} (hI : I ∈ a)
    (hmax : ∀ J ∈ a, J ≤ I) :
    round a = some ⟨I, (chain (a.erase I) (I.ending - 1) I.beginning).1,
      (chain (a.erase I) (I.ending - 1) I.beginning).2⟩ := by
  obtain ⟨r, hr⟩ : ∃ r, round a = some r := by
    cases h : round a with
    | none =>
      have := (round_none_iff a).mp h
      subst this
      simp at hI
    | some r => exact ⟨r, rfl⟩
  have hfirst : r.first = I :=
    le_antisymm (hmax _ (Langlands.MoeglinWaldspurger.round_first_mem hr)) (round_first_maximal hr hI)
  have hc := round_chain_eq hr
  obtain ⟨f, t, u⟩ := r
  simp only at hfirst hc
  subst hfirst
  rw [hc, hr]

/-! ### Shortening -/

theorem shorten_cons (I : Interval) (s : Multisegment) :
    shorten (I ::ₘ s) = I.dropLast + shorten s := by
  unfold shorten; rw [Multiset.cons_bind]

theorem shorten_add (s t : Multisegment) : shorten (s + t) = shorten s + shorten t := by
  unfold shorten; rw [Multiset.add_bind]

theorem shorten_singleton (I : Interval) : shorten {I} = I.dropLast := by
  unfold shorten; rw [Multiset.singleton_bind]

theorem mem_shorten {s : Multisegment} {J : Interval} (h : J ∈ shorten s) :
    ∃ I ∈ s, J.beginning = I.beginning ∧ J.ending = I.ending - 1 := by
  obtain ⟨I, hI, hJ⟩ := Multiset.mem_bind.mp h
  exact ⟨I, hI, mem_dropLast hJ⟩

theorem shorten_erase_of_mem {U : Multisegment} {Δ : Interval} (h : Δ ∈ U) :
    shorten U = Δ.dropLast + shorten (U.erase Δ) := by
  conv_lhs => rw [← Multiset.cons_erase h]
  exact shorten_cons _ _

/-- The multiset identity behind the case of a round selecting one occurrence. -/
theorem sub_add_shorten_eq {a U D : Multisegment} {F : Interval} (hFU : F ∈ U) (hUa : U ≤ a)
    (hD : ∀ J ∈ D, J ∉ U) (S : Multisegment) :
    a - U + (D + S) = a.erase F + D - U.erase F + S := by
  ext J
  have hle := Multiset.count_le_of_le J hUa
  simp only [Multiset.count_add, Multiset.count_sub]
  by_cases hJ : J = F
  · subst hJ
    have hF : 0 < Multiset.count J U := Multiset.count_pos.mpr hFU
    have hD0 : Multiset.count J D = 0 := Multiset.count_eq_zero.mpr (fun h => hD J h hFU)
    rw [Multiset.count_erase_self, Multiset.count_erase_self, hD0]
    omega
  · rw [Multiset.count_erase_of_ne hJ, Multiset.count_erase_of_ne hJ]
    by_cases hd : J ∈ D
    · have hu : Multiset.count J U = 0 := Multiset.count_eq_zero.mpr (hD J hd)
      rw [hu]; omega
    · rw [Multiset.count_eq_zero.mpr hd]; omega

/-- The multiset identity behind the residual in the case of several selections. -/
theorem residual_identity {a a' S₀ u u' U : Multisegment} {Δ : Interval}
    (hΔU : Δ ∈ U) (hUa : U ≤ a) (hpart : S₀ + {Δ} + u = a) (hpart' : S₀ + u' = a')
    (ha' : a' = a - U + shorten U)
    (hS₀U : ∀ J ∈ S₀, J ∉ U) (hS₀D : ∀ J ∈ S₀, J ∉ Δ.dropLast)
    (hS₀sh : ∀ J ∈ S₀, J ∉ shorten (U.erase Δ)) (hDU : ∀ J ∈ Δ.dropLast, J ∉ U) :
    u' + shorten S₀ = u + shorten (S₀ + {Δ}) - U.erase Δ + shorten (U.erase Δ) := by
  rw [shorten_erase_of_mem hΔU] at ha'
  rw [shorten_add, shorten_singleton]
  ext J
  have hle := Multiset.count_le_of_le J hUa
  have e1 := congrArg (Multiset.count J) hpart
  have e2 := congrArg (Multiset.count J) hpart'
  have e3 := congrArg (Multiset.count J) ha'
  simp only [Multiset.count_add, Multiset.count_sub] at e1 e2 e3 ⊢
  by_cases hJΔ : J = Δ
  · subst hJΔ
    have hpos := Multiset.count_pos.mpr hΔU
    have hs : Multiset.count J S₀ = 0 := Multiset.count_eq_zero.mpr (fun h => hS₀U J h hΔU)
    have hd : Multiset.count J J.dropLast = 0 :=
      Multiset.count_eq_zero.mpr (fun h => hDU J h hΔU)
    rw [Multiset.count_singleton_self] at e1
    rw [Multiset.count_erase_self]
    omega
  · simp only [Multiset.count_singleton, hJΔ, ↓reduceIte] at e1
    rw [Multiset.count_erase_of_ne hJΔ]
    by_cases hs : J ∈ S₀
    · have h1 : Multiset.count J U = 0 := Multiset.count_eq_zero.mpr (hS₀U J hs)
      have h2 : Multiset.count J Δ.dropLast = 0 := Multiset.count_eq_zero.mpr (hS₀D J hs)
      have h3 : Multiset.count J (shorten (U.erase Δ)) = 0 :=
        Multiset.count_eq_zero.mpr (hS₀sh J hs)
      omega
    · have h0 : Multiset.count J S₀ = 0 := Multiset.count_eq_zero.mpr hs
      by_cases hd : J ∈ Δ.dropLast
      · have h1 : Multiset.count J U = 0 := Multiset.count_eq_zero.mpr (hDU J hd)
        omega
      · have h2 : Multiset.count J Δ.dropLast = 0 := Multiset.count_eq_zero.mpr hd
        omega

/-! ### The chain compatibility -/

/-- **Chain compatibility of the bottom-up matching.** -/
theorem chainUnmatchedCompatibility : ChainUnmatchedCompatibility := by
  intro a r hr
  obtain ⟨F, t, u⟩ := r
  have hpart := round_partition hr
  have hchain := round_chain_eq hr
  have hFmem := Langlands.MoeglinWaldspurger.round_first_mem hr
  have hmaxF : ∀ I ∈ a, I ≤ F := fun I hI => round_first_maximal hr hI
  simp only [Round.selected, Round.selectedList] at hpart hchain hFmem
  simp only [Round.emitted, Round.residual, Round.selected, Round.selectedList]
  by_cases ht : t = []
  · -- a round selecting one occurrence
    subst ht
    simp only [List.length_nil, Nat.cast_zero, sub_zero]
    have hu : u = a.erase F := by
      rw [← hpart]; simp
    subst hu
    have hshF : shorten (([F] : List Interval) : Multisegment) = F.dropLast := by
      rw [Multiset.coe_singleton, shorten_singleton]
    rw [hshF]
    have hstop : ∀ I ∈ a, I.ending = F.ending - 1 → F.beginning ≤ I.beginning := by
      have hpn : pick (a.erase F) (F.ending - 1) F.beginning = none := by
        rw [← chain_eq_nil_iff, hchain]
      intro I hI hIe
      have hI' : I ∈ a.erase F := (Multiset.mem_erase_of_ne (by rintro rfl; omega)).mpr hI
      rcases (Langlands.MoeglinWaldspurger.Involution.pick_none_iff _ _ _).mp hpn I hI' with h | h
      · omega
      · exact h
    have hmaxc : ∀ I ∈ a, I.ending = F.ending → I.beginning ≤ F.beginning := by
      intro I hI hIe
      rcases (Langlands.MoeglinWaldspurger.Involution.interval_le_iff _ _).mp (hmaxF I hI) with h | ⟨-, h⟩
      · omega
      · exact h
    obtain ⟨hPU, hU'⟩ := unmatched_erase_last (b := a) (c := F.ending) (γ := F.beginning + 1)
      (E := 0) hFmem rfl (by omega) hstop (fun I hI hIe => Or.inl (hmaxc I hI hIe))
      (Or.inr ⟨rfl, hmaxc⟩)
    rw [add_zero] at hU'
    have hFU : F ∈ unmatched a F.ending :=
      Multiset.mem_of_le hPU (Multiset.mem_filter.mpr ⟨hFmem, rfl, le_rfl⟩)
    refine ⟨?_, ?_, fun h => absurd rfl h⟩
    · rw [hU', Multiset.card_erase_add_one hFU]
    · intro _
      unfold leftDerivative
      rw [hU', shorten_erase_of_mem hFU]
      exact sub_add_shorten_eq hFU (unmatched_le a _) (fun J hJ hJU => by
        have h1 := (mem_dropLast hJ).2
        have h2 := mem_unmatched_ending hJU
        omega) _
  · -- a round selecting several occurrences
    have hne : (chain (a.erase F) (F.ending - 1) F.beginning).1 ≠ [] := by
      rw [hchain]; exact ht
    obtain ⟨L₀, Δ, hL, hΔm, hΔe, hΔb, hmax, hstop, hhigh, hprev⟩ := chain_last _ _ _ hne
    rw [hchain] at hL
    dsimp only at hL
    subst hL
    have hc : F.ending - (((L₀ ++ [Δ]).length : ℕ) : ℤ) = Δ.ending := by
      simp only [List.length_append, List.length_singleton]; push_cast; omega
    rw [hc]
    have hΔa : Δ ∈ a := Multiset.mem_of_mem_erase hΔm
    have hFΔ : Δ.ending < F.ending := by omega
    have hmemF : ∀ I ∈ a, I.ending ≤ Δ.ending → I ∈ a.erase F := fun I hI hIe =>
      (Multiset.mem_erase_of_ne (by rintro rfl; omega)).mpr hI
    generalize hγ : (L₀.map Interval.beginning).getLastD F.beginning = γ at hΔb hmax
    obtain ⟨L₂, Δ', hL₂, hΔ'e, hΔ'b, hL₂high⟩ : ∃ (L₂ : List Interval) (Δ' : Interval),
        F :: L₀ = L₂ ++ [Δ'] ∧ Δ'.ending = Δ.ending + 1 ∧ Δ'.beginning = γ ∧
          ∀ K ∈ L₂, Δ.ending + 1 < K.ending := by
      rcases hprev with rfl | ⟨L₁, Δ', rfl, h1, h2⟩
      · refine ⟨[], F, rfl, by simp at hΔe; omega, by rw [← hγ]; simp, by simp⟩
      · refine ⟨F :: L₁, Δ', rfl, h1, by rw [← hγ]; simp, ?_⟩
        intro K hK
        rcases List.mem_cons.mp hK with rfl | hK
        · simp at hΔe; omega
        · exact h2 K hK
    have h1 : ∀ I ∈ a, I.ending = Δ.ending - 1 → Δ.beginning ≤ I.beginning :=
      fun I hI hIe => hstop I (hmemF I hI (by omega)) hIe
    have h2 : ∀ I ∈ a, I.ending = Δ.ending → I.beginning ≤ Δ.beginning ∨ γ ≤ I.beginning := by
      intro I hI hIe
      by_cases hb : I.beginning < γ
      · exact Or.inl (hmax I (hmemF I hI hIe.le) hIe hb)
      · exact Or.inr (not_lt.mp hb)
    have hE : (∃ hγ' : γ ≤ Δ.ending, Δ'.dropLast = {⟨γ, Δ.ending, hγ'⟩}) ∨
        (Δ'.dropLast = 0 ∧ ∀ I ∈ a, I.ending = Δ.ending → I.beginning ≤ Δ.beginning) := by
      by_cases hγc : γ ≤ Δ.ending
      · left
        refine ⟨hγc, ?_⟩
        rw [dropLast_of_lt (by omega)]
        congr 1
        exact Interval.ext hΔ'b (by show Δ'.ending - 1 = Δ.ending; omega)
      · right
        refine ⟨?_, ?_⟩
        · simp only [Interval.dropLast, show ¬ Δ'.beginning < Δ'.ending by
            have := Δ'.nonempty; omega, ↓reduceDIte]
        · intro I hI hIe
          rcases h2 I hI hIe with h | h
          · exact h
          · have := I.nonempty; omega
    obtain ⟨hPU, hU'⟩ := unmatched_erase_last hΔa rfl hΔb h1 h2 hE
    have hΔU : Δ ∈ unmatched a Δ.ending :=
      Multiset.mem_of_le hPU (Multiset.mem_filter.mpr ⟨hΔa, rfl, le_rfl⟩)
    have hUe : ∀ J ∈ unmatched a Δ.ending, J.ending = Δ.ending :=
      fun J hJ => mem_unmatched_ending hJ
    -- the selected occurrences
    have hS₀ : (((F :: L₀ : List Interval)) : Multisegment) = ↑L₂ + {Δ'} := by
      rw [hL₂, ← Multiset.coe_add, Multiset.coe_singleton]
    have hsel : (((F :: (L₀ ++ [Δ]) : List Interval)) : Multisegment) = ↑L₂ + {Δ'} + {Δ} := by
      rw [← List.cons_append, ← Multiset.coe_add, hS₀, Multiset.coe_singleton]
    have hS₀e : ∀ J ∈ (↑L₂ + {Δ'} : Multisegment), Δ.ending < J.ending := by
      intro J hJ
      rcases Multiset.mem_add.mp hJ with hJ | hJ
      · have := hL₂high J (Multiset.mem_coe.mp hJ); omega
      · rw [Multiset.mem_singleton] at hJ; subst hJ; omega
    rw [hsel] at hpart
    rw [hsel]
    -- the two relevant endings of the residual
    have hres : (u + shorten (↑L₂ + {Δ'} + {Δ})).filter (TwoEnd Δ.ending) =
        (a.erase Δ + Δ.dropLast + Δ'.dropLast).filter (TwoEnd Δ.ending) := by
      rw [← hpart]
      have f1 : (↑L₂ : Multisegment).filter (TwoEnd Δ.ending) = 0 :=
        Multiset.filter_eq_nil.mpr fun K hK => by
          have := hL₂high K (Multiset.mem_coe.mp hK); unfold TwoEnd; omega
      have f2 : (shorten ↑L₂).filter (TwoEnd Δ.ending) = 0 :=
        Multiset.filter_eq_nil.mpr fun K hK => by
          obtain ⟨K', hK', -, hKe⟩ := mem_shorten hK
          have := hL₂high K' (Multiset.mem_coe.mp hK'); unfold TwoEnd; omega
      have f3 : ({Δ'} : Multisegment).filter (TwoEnd Δ.ending) = 0 :=
        Multiset.filter_eq_nil.mpr fun K hK => by
          rw [Multiset.mem_singleton] at hK; subst hK; unfold TwoEnd; omega
      have f4 : Δ.dropLast.filter (TwoEnd Δ.ending) = Δ.dropLast :=
        Multiset.filter_eq_self.mpr fun K hK => Or.inr (mem_dropLast hK).2
      have f5 : Δ'.dropLast.filter (TwoEnd Δ.ending) = Δ'.dropLast :=
        Multiset.filter_eq_self.mpr fun K hK => Or.inl (by have := (mem_dropLast hK).2; omega)
      have herase : (↑L₂ + {Δ'} + {Δ} + u).erase Δ = ↑L₂ + {Δ'} + u := by
        rw [Multiset.erase_add_left_pos _
            (Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self Δ))),
          Multiset.erase_add_right_pos _ (Multiset.mem_singleton_self Δ),
          Multiset.erase_singleton, add_zero]
      rw [herase]
      simp only [shorten_add, shorten_singleton, Multiset.filter_add, f1, f2, f3, f4, f5]
      abel
    have hUres : unmatched (u + shorten (↑L₂ + {Δ'} + {Δ})) Δ.ending =
        (unmatched a Δ.ending).erase Δ := by
      rw [← unmatched_filter, hres, unmatched_filter, hU']
    refine ⟨?_, fun h => absurd h (by simp), ?_⟩
    · rw [hUres, Multiset.card_erase_add_one hΔU]
    · intro _
      obtain ⟨a', ha'⟩ : ∃ a', a' = leftDerivative a Δ.ending := ⟨_, rfl⟩
      rw [← ha']
      have hFa' : F ∈ a' := by
        rw [ha']
        unfold leftDerivative
        refine Multiset.mem_add.mpr (Or.inl (Multiset.mem_sub.mpr ?_))
        have h0 : Multiset.count F (unmatched a Δ.ending) = 0 :=
          Multiset.count_eq_zero.mpr (fun h => by have := hUe F h; omega)
        rw [h0]; exact Multiset.count_pos.mpr hFmem
      have hmax' : ∀ J ∈ a', J ≤ F := by
        intro J hJ
        rw [ha'] at hJ
        unfold leftDerivative at hJ
        rcases Multiset.mem_add.mp hJ with hJ | hJ
        · exact hmaxF J (Multiset.mem_of_le tsub_le_self hJ)
        · obtain ⟨K, hK, -, hKe⟩ := mem_shorten hJ
          have := hUe K hK
          exact (Langlands.MoeglinWaldspurger.Involution.interval_le_iff _ _).mpr (Or.inl (by omega))
      have hround' := round_eq_of_max hFa' hmax'
      -- the part above `Δ.ending` is unchanged
      have hfa : a'.filter (fun I => Δ.ending < I.ending) =
          a.filter (fun I => Δ.ending < I.ending) := by
        have g1 : (unmatched a Δ.ending).filter (fun I => Δ.ending < I.ending) = 0 :=
          Multiset.filter_eq_nil.mpr (fun J hJ hlt => by have := hUe J hJ; omega)
        have g2 : (shorten (unmatched a Δ.ending)).filter (fun I => Δ.ending < I.ending) = 0 :=
          Multiset.filter_eq_nil.mpr (fun J hJ hlt => by
            obtain ⟨K, hK, -, hKe⟩ := mem_shorten hJ; have := hUe K hK; omega)
        rw [ha']
        unfold leftDerivative
        rw [Multiset.filter_add, Multiset.filter_sub, g1, g2, tsub_zero, add_zero]
      have hfa' : (a'.erase F).filter (fun I => Δ.ending < I.ending) =
          (a.erase F).filter (fun I => Δ.ending < I.ending) := by
        rw [filter_erase_of_pos _ hFΔ, filter_erase_of_pos _ hFΔ, hfa]
      have hch1 : chain ((a.erase F).filter (fun I => Δ.ending < I.ending)) (F.ending - 1)
          F.beginning = (L₀, u.filter (fun I => Δ.ending < I.ending)) := by
        rw [chain_filter_gt, hchain]
        have hfl : (L₀ ++ [Δ]).filter (fun I => decide (Δ.ending < I.ending)) = L₀ := by
          rw [List.filter_append, List.filter_eq_self.mpr
            (fun K hK => by simpa using hhigh K hK)]
          simp
        dsimp only
        rw [hfl]
      have hcond : ∀ I ∈ (a'.erase F).filter (fun I => ¬ Δ.ending < I.ending),
          I.ending < (F.ending - 1) - ((chain ((a'.erase F).filter
            (fun I => Δ.ending < I.ending)) (F.ending - 1) F.beginning).1.length : ℤ) ∨
          (I.ending = (F.ending - 1) - ((chain ((a'.erase F).filter
            (fun I => Δ.ending < I.ending)) (F.ending - 1) F.beginning).1.length : ℤ) ∧
            ((chain ((a'.erase F).filter (fun I => Δ.ending < I.ending)) (F.ending - 1)
              F.beginning).1.map Interval.beginning).getLastD F.beginning ≤ I.beginning) := by
        rw [hfa', hch1]
        dsimp only
        rw [hγ]
        intro I hI
        obtain ⟨hI', hle⟩ := Multiset.mem_filter.mp hI
        have hIa' := Multiset.mem_of_mem_erase hI'
        rcases lt_or_eq_of_le (not_lt.mp hle) with hlt | heq
        · left; omega
        · right
          refine ⟨by omega, ?_⟩
          rw [ha'] at hIa'
          unfold leftDerivative at hIa'
          rcases Multiset.mem_add.mp hIa' with hIs | hIs
          · have hcnt := Multiset.mem_sub.mp hIs
            have hIa : I ∈ a := Multiset.mem_of_le tsub_le_self hIs
            rcases h2 I hIa heq with hb | hb
            · exfalso
              have hP : Multiset.count I (a.filter
                  (fun J => J.ending = Δ.ending ∧ J.beginning ≤ Δ.beginning)) =
                  Multiset.count I a := by
                simp [heq, hb]
              have := Multiset.count_le_of_le I hPU
              omega
            · exact hb
          · exfalso
            obtain ⟨K, hK, -, hKe⟩ := mem_shorten hIs
            have := hUe K hK
            omega
      have hch2 : chain (a'.erase F) (F.ending - 1) F.beginning =
          (L₀, u.filter (fun I => Δ.ending < I.ending) +
            (a'.erase F).filter (fun I => ¬ Δ.ending < I.ending)) := by
        conv_lhs => rw [← Multiset.filter_add_not (fun I => Δ.ending < I.ending) (a'.erase F)]
        rw [chain_add_low _ _ _ _ hcond, hfa', hch1]
      rw [hch2] at hround'
      refine ⟨_, hround', ?_, rfl, ?_⟩
      · show F.ending - (L₀.length : ℤ) = Δ.ending + 1
        omega
      · have hpart' := round_partition hround'
        simp only [Round.selected, Round.selectedList] at hpart'
        rw [hS₀] at hpart'
        show _ + shorten ((F :: L₀ : List Interval) : Multisegment) = _
        rw [hS₀]
        unfold leftDerivative
        rw [hUres]
        refine residual_identity hΔU (unmatched_le a _) hpart hpart' ha' ?_ ?_ ?_ ?_
        · intro J hJ hJU
          have := hS₀e J hJ; have := hUe J hJU; omega
        · intro J hJ hJD
          have := hS₀e J hJ; have := (mem_dropLast hJD).2; omega
        · intro J hJ hJs
          have := hS₀e J hJ
          obtain ⟨K, hK, -, hKe⟩ := mem_shorten hJs
          have := hUe K (Multiset.mem_of_mem_erase hK)
          omega
        · intro J hJD hJU
          have := (mem_dropLast hJD).2; have := hUe J hJU; omega

end Langlands.MoeglinWaldspurger.Derivation
