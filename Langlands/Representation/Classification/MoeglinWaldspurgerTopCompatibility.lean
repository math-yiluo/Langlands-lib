import Langlands.Representation.Classification.MoeglinWaldspurgerChainCompatibility

/-!
# The top compatibility of the bottom-up matching

Proof of `TopUnmatchedCompatibility`, through a generalization to every input whose endings
are at most `x`.
-/

namespace Langlands.MoeglinWaldspurger.Derivation

open Langlands.MoeglinWaldspurger

/-! ### Scanning blocks of occurrences ending at `x` -/

theorem unmatchedScan_of_ending_eq_drop (x : ℤ) :
    ∀ (l : List Interval) (pool : ℕ), (∀ I ∈ l, I.ending = x) →
      unmatchedScan x l pool = l.drop pool ∧ scanPool x l pool = pool - l.length
  | [], p, _ => by simp [unmatchedScan, scanPool]
  | I :: l, p, h => by
    have hI : I.ending = x := h I (List.mem_cons_self ..)
    have ih := fun q => unmatchedScan_of_ending_eq_drop x l q
      (fun J hJ => h J (List.mem_cons_of_mem _ hJ))
    simp only [unmatchedScan, scanPool, hI, show ¬ x = x - 1 by omega, ↓reduceIte]
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp [(ih 0).1, (ih 0).2]
    · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      simp [(ih q).1, (ih q).2]

theorem sort_eq_append_max {m : Multisegment} {Δ : Interval} (hΔ : Δ ∈ m)
    (h : ∀ I ∈ m.erase Δ, ScanLE I Δ) :
    m.sort ScanLE = (m.erase Δ).sort ScanLE ++ [Δ] := by
  conv_lhs => rw [← Multiset.cons_erase hΔ, ← Multiset.singleton_add, add_comm]
  rw [sort_add_of_scanLE _ _ (fun I hI J hJ => by
    rw [Multiset.mem_singleton] at hJ; subst hJ; exact h I hI), Multiset.sort_singleton]

theorem mem_unmatchedScan (x : ℤ) (l : List Interval) (pool : ℕ) {I : Interval}
    (h : I ∈ unmatchedScan x l pool) : I ∈ l :=
  (unmatchedScan_sublist x l pool).subset h

/-- **Top scan lemma.** Let `F` be an occurrence ending at `x` with the greatest beginning,
and `Δ` the occurrence ending at `x - 1` with the greatest beginning below that of `F`.
Removing both and adding the shortening of `F` either leaves the unmatched occurrences
unchanged (when `F` is matched) or exchanges `F` for the last matched occurrence `G`. -/
theorem unmatched_top {b : Multisegment} {x : ℤ} {F Δ : Interval}
    (hF : F ∈ b) (hFx : F.ending = x)
    (hFmax : ∀ I ∈ b, I.ending = x → I.beginning ≤ F.beginning)
    (hΔ : Δ ∈ b) (hΔx : Δ.ending = x - 1) (hΔF : Δ.beginning < F.beginning)
    (hΔmax : ∀ I ∈ b, I.ending = x - 1 → I.beginning < F.beginning →
      I.beginning ≤ Δ.beginning) :
    (F ∉ unmatched b x ∧ unmatched ((b.erase F).erase Δ + F.dropLast) x = unmatched b x ∧
        ∀ I ∈ unmatched b x, I.beginning ≤ Δ.beginning) ∨
    (F ∈ unmatched b x ∧ ∃ G ∈ b, G.ending = x ∧ Δ.beginning < G.beginning ∧
        Multiset.count G (unmatched b x) < Multiset.count G b ∧
        unmatched ((b.erase F).erase Δ + F.dropLast) x = (unmatched b x).erase F + {G} ∧
        (∀ I ∈ unmatched b x, I.beginning ≤ Δ.beginning ∨ G.beginning ≤ I.beginning) ∧
        (∀ I ∈ b, I.ending = x → G.beginning < I.beginning →
          Multiset.count I (unmatched b x) = Multiset.count I b)) := by
  generalize hβ : Δ.beginning = β at hΔF hΔmax ⊢
  obtain ⟨B₁, hB₁⟩ : ∃ B, B = b.filter (fun I => TwoEnd x I ∧ I.beginning ≤ β) := ⟨_, rfl⟩
  obtain ⟨B₂, hB₂⟩ : ∃ B, B = b.filter (fun I => I.ending = x ∧ β < I.beginning) := ⟨_, rfl⟩
  obtain ⟨B₃, hB₃⟩ : ∃ B, B = b.filter (fun I => I.ending = x - 1 ∧ β < I.beginning) :=
    ⟨_, rfl⟩
  have m₁ : ∀ I ∈ B₁, I ∈ b ∧ TwoEnd x I ∧ I.beginning ≤ β := by
    intro I hI; rw [hB₁] at hI; exact ⟨(Multiset.mem_filter.mp hI).1, (Multiset.mem_filter.mp hI).2⟩
  have m₂ : ∀ I ∈ B₂, I ∈ b ∧ I.ending = x ∧ β < I.beginning := by
    intro I hI; rw [hB₂] at hI; exact ⟨(Multiset.mem_filter.mp hI).1, (Multiset.mem_filter.mp hI).2⟩
  have m₃ : ∀ I ∈ B₃, I ∈ b ∧ I.ending = x - 1 ∧ β < I.beginning := by
    intro I hI; rw [hB₃] at hI; exact ⟨(Multiset.mem_filter.mp hI).1, (Multiset.mem_filter.mp hI).2⟩
  have hΔB₁ : Δ ∈ B₁ := by
    rw [hB₁]; exact Multiset.mem_filter.mpr ⟨hΔ, Or.inr hΔx, hβ.le⟩
  have hFB₂ : F ∈ B₂ := by
    rw [hB₂]; exact Multiset.mem_filter.mpr ⟨hF, hFx, hΔF⟩
  have hJ : b.filter (TwoEnd x) = B₁ + B₂ + B₃ := by
    ext I
    rw [hB₁, hB₂, hB₃]
    simp only [Multiset.count_add, Multiset.count_filter]
    unfold TwoEnd
    have hx : x - 1 ≠ x := by omega
    by_cases e1 : I.ending = x
    · by_cases e3 : I.beginning ≤ β
      · simp [e1, e3, hx.symm]
      · simp [e1, e3, show β < I.beginning by omega, hx.symm]
    · by_cases e2 : I.ending = x - 1
      · by_cases e3 : I.beginning ≤ β
        · simp [e2, e3, hx]
        · simp [e2, e3, show β < I.beginning by omega, hx]
      · simp [e1, e2]
  -- orders
  have o₁₂ : ∀ I ∈ B₁, ∀ J ∈ B₂, ScanLE I J := by
    intro I hI J hJ
    have := (m₁ I hI).2.2; have := (m₂ J hJ).2.2
    unfold ScanLE; omega
  have o₂₃ : ∀ I ∈ B₂, ∀ J ∈ B₃, ScanLE I J := by
    intro I hI J hJ
    obtain ⟨hIb, hIe, -⟩ := m₂ I hI
    obtain ⟨hJb, hJe, hJβ⟩ := m₃ J hJ
    have h1 := hFmax I hIb hIe
    have h2 : F.beginning ≤ J.beginning := by
      by_contra hlt
      have := hΔmax J hJb hJe (by omega)
      omega
    unfold ScanLE; omega
  have o₁₃ : ∀ I ∈ B₁ + B₂, ∀ J ∈ B₃, ScanLE I J := by
    intro I hI J hJ
    rcases Multiset.mem_add.mp hI with hI | hI
    · have := (m₁ I hI).2.2; have := (m₃ J hJ).2.2
      unfold ScanLE; omega
    · exact o₂₃ I hI J hJ
  have hB₁sort : B₁.sort ScanLE = (B₁.erase Δ).sort ScanLE ++ [Δ] := by
    apply sort_eq_append_max hΔB₁
    intro I hI
    obtain ⟨-, hIt, hIβ⟩ := m₁ I (Multiset.mem_of_mem_erase hI)
    unfold TwoEnd at hIt
    unfold ScanLE; omega
  have hB₂sort : B₂.sort ScanLE = (B₂.erase F).sort ScanLE ++ [F] := by
    apply sort_eq_append_max hFB₂
    intro I hI
    obtain ⟨hIb, hIe, -⟩ := m₂ I (Multiset.mem_of_mem_erase hI)
    have := hFmax I hIb hIe
    unfold ScanLE; omega
  have hΔscan : unmatchedScan x [Δ] = fun p => [] := by
    funext p; simp [unmatchedScan, hΔx]
  have hΔpool : scanPool x [Δ] = fun p => p + 1 := by
    funext p; simp [scanPool, hΔx]
  have hall₂ : ∀ I ∈ (B₂.erase F).sort ScanLE ++ [F], I.ending = x := by
    intro I hI
    rcases List.mem_append.mp hI with hI | hI
    · exact (m₂ I (Multiset.mem_of_mem_erase ((Multiset.mem_sort _).mp hI))).2.1
    · rw [List.mem_singleton] at hI; subst hI; exact hFx
  have hall₂' : ∀ I ∈ (B₂.erase F).sort ScanLE, I.ending = x := fun I hI =>
    hall₂ I (List.mem_append_left _ hI)
  have hall₃ : ∀ I ∈ B₃.sort ScanLE, I.ending = x - 1 := fun I hI =>
    (m₃ I ((Multiset.mem_sort _).mp hI)).2.1
  obtain ⟨R, hR⟩ : ∃ R, R = unmatchedScan x ((B₁.erase Δ).sort ScanLE) 0 := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = scanPool x ((B₁.erase Δ).sort ScanLE) 0 := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = (B₂.erase F).sort ScanLE := ⟨_, rfl⟩
  have hU : unmatched b x = (R : Multiset Interval) + ((L ++ [F]).drop (P + 1) : List Interval) := by
    rw [← unmatched_filter, hJ, unmatched_three_blocks x B₁ B₂ B₃ o₁₂ o₁₃, hB₁sort, hB₂sort,
      unmatchedScan_append, scanPool_append, hΔscan, hΔpool, ← hR, ← hP, ← hL]
    rw [← hL] at hall₂
    rw [(unmatchedScan_of_ending_eq_drop x _ _ hall₂).1,
      (unmatchedScan_of_ending_eq_sub_one x _ _ hall₃).1]
    simp only [List.append_nil, ← Multiset.coe_add]
  -- the modified input
  have hFdl : F.dropLast.filter (TwoEnd x) = F.dropLast :=
    Multiset.filter_eq_self.mpr (fun K hK => Or.inr (by have := (mem_dropLast hK).2; omega))
  have hJ' : ((b.erase F).erase Δ + F.dropLast).filter (TwoEnd x) =
      B₁.erase Δ + B₂.erase F + (F.dropLast + B₃) := by
    rw [Multiset.filter_add, filter_erase_of_pos _ (show TwoEnd x Δ from Or.inr hΔx),
      filter_erase_of_pos _ (show TwoEnd x F from Or.inl hFx), hJ,
      Multiset.erase_add_left_pos _ (Multiset.mem_add.mpr (Or.inr hFB₂)),
      Multiset.erase_add_right_pos _ hFB₂,
      Multiset.erase_add_left_pos _ (Multiset.mem_add.mpr (Or.inl hΔB₁)),
      Multiset.erase_add_left_pos _ hΔB₁, hFdl]
    abel
  have o'₁₂ : ∀ I ∈ B₁.erase Δ, ∀ J ∈ B₂.erase F, ScanLE I J := fun I hI J hJ =>
    o₁₂ I (Multiset.mem_of_mem_erase hI) J (Multiset.mem_of_mem_erase hJ)
  have o'₁₃ : ∀ I ∈ B₁.erase Δ + B₂.erase F, ∀ J ∈ F.dropLast + B₃, ScanLE I J := by
    intro I hI J hJ
    rcases Multiset.mem_add.mp hJ with hJ | hJ
    · obtain ⟨hJb, hJe⟩ := mem_dropLast hJ
      rcases Multiset.mem_add.mp hI with hI | hI
      · have := (m₁ I (Multiset.mem_of_mem_erase hI)).2.2
        unfold ScanLE; omega
      · obtain ⟨hIb, hIe, -⟩ := m₂ I (Multiset.mem_of_mem_erase hI)
        have := hFmax I hIb hIe
        unfold ScanLE; omega
    · exact o₁₃ I (by
        rcases Multiset.mem_add.mp hI with hI | hI
        · exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_of_mem_erase hI))
        · exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_of_mem_erase hI))) J hJ
  have hall₃' : ∀ I ∈ (F.dropLast + B₃).sort ScanLE, I.ending = x - 1 := by
    intro I hI
    rcases Multiset.mem_add.mp ((Multiset.mem_sort _).mp hI) with hI | hI
    · have := (mem_dropLast hI).2; omega
    · exact (m₃ I hI).2.1
  have hU' : unmatched ((b.erase F).erase Δ + F.dropLast) x =
      (R : Multiset Interval) + (L.drop P : List Interval) := by
    rw [← unmatched_filter, hJ', unmatched_three_blocks x _ _ _ o'₁₂ o'₁₃, ← hR, ← hP, ← hL]
    rw [← hL] at hall₂'
    rw [(unmatchedScan_of_ending_eq_drop x _ _ hall₂').1,
      (unmatchedScan_of_ending_eq_sub_one x _ _ hall₃').1]
    simp only [List.append_nil, ← Multiset.coe_add]
  -- facts about `R` and `L`
  have hRβ : ∀ I ∈ R, I.beginning ≤ β := by
    intro I hI
    rw [hR] at hI
    exact (m₁ I (Multiset.mem_of_mem_erase ((Multiset.mem_sort _).mp
      (mem_unmatchedScan x _ 0 hI)))).2.2
  have hLsorted : L.Pairwise ScanLE := by rw [hL]; exact Multiset.pairwise_sort _ _
  have hLmem : ∀ I ∈ L, I ∈ B₂ := by
    intro I hI; rw [hL] at hI
    exact Multiset.mem_of_mem_erase ((Multiset.mem_sort _).mp hI)
  have hLcount : ∀ I, List.count I L + Multiset.count I ({F} : Multisegment) =
      Multiset.count I B₂ := by
    intro I
    have : (L : Multisegment) + {F} = B₂ := by
      rw [hL, Multiset.sort_eq, ← Multiset.cons_erase hFB₂, Multiset.erase_cons_head,
        add_comm, Multiset.singleton_add]
    rw [← this, Multiset.count_add, Multiset.coe_count]
  have hFR : F ∉ R := fun h => by have := hRβ F h; omega
  by_cases hPL : P < L.length
  · right
    have hdrop : L.drop P = L[P] :: L.drop (P + 1) := List.drop_eq_getElem_cons hPL
    have hdrop' : (L ++ [F]).drop (P + 1) = L.drop (P + 1) ++ [F] :=
      List.drop_append_of_le_length (by omega)
    obtain ⟨G, hG⟩ : ∃ G, G = L[P] := ⟨_, rfl⟩
    have hGL : G ∈ L := by rw [hG]; exact List.getElem_mem hPL
    obtain ⟨hGb, hGx, hGβ⟩ := m₂ G (hLmem G hGL)
    have htake : L.take (P + 1) = L.take P ++ [G] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hPL, ← hG]; rfl
    have hsplit : L = L.take P ++ [G] ++ L.drop (P + 1) := by
      rw [← htake, List.take_append_drop]
    have hpw := hLsorted
    rw [hsplit, List.pairwise_append, List.pairwise_append] at hpw
    obtain ⟨⟨-, -, hbefore⟩, -, hafter⟩ := hpw
    have hafterG : ∀ I ∈ L.drop (P + 1), ScanLE G I := fun I hI =>
      hafter G (List.mem_append_right _ (List.mem_singleton_self G)) I hI
    have hbeforeG : ∀ I ∈ L.take P, ScanLE I G := fun I hI =>
      hbefore I hI G (List.mem_singleton_self G)
    rw [hdrop', ← Multiset.coe_add, Multiset.coe_singleton] at hU
    rw [hdrop, ← hG] at hU'
    have hFU : F ∈ unmatched b x := by
      rw [hU]; exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_add.mpr
        (Or.inr (Multiset.mem_singleton_self F))))
    refine ⟨hFU, G, hGb, hGx, hβ ▸ hGβ, ?_, ?_, ?_, ?_⟩
    · -- `G` is matched at least once
      have h1 : Multiset.count G (R : Multisegment) = 0 :=
        Multiset.count_eq_zero.mpr (fun h => by have := hRβ G h; omega)
      have h2 := hLcount G
      have h3 : Multiset.count G B₂ ≤ Multiset.count G b := by
        rw [hB₂]; exact Multiset.count_le_of_le _ (Multiset.filter_le _ _)
      have h4 : List.count G L = List.count G (L.take P) + 1 + List.count G (L.drop (P + 1)) := by
        conv_lhs => rw [hsplit]
        simp only [List.count_append, List.count_singleton_self]
      rw [hU, Multiset.count_add, Multiset.count_add, h1, Multiset.coe_count]
      omega
    · rw [hU, hU', Multiset.erase_add_right_pos _ (Multiset.mem_add.mpr
        (Or.inr (Multiset.mem_singleton_self F))),
        Multiset.erase_add_right_pos _ (Multiset.mem_singleton_self F),
        Multiset.erase_singleton, add_zero, ← Multiset.cons_coe, add_assoc,
        Multiset.add_comm _ {G}, Multiset.singleton_add]
    · intro I hI
      rw [hU] at hI
      rcases Multiset.mem_add.mp hI with hI | hI
      · exact Or.inl (hβ ▸ hRβ I hI)
      · rcases Multiset.mem_add.mp hI with hI | hI
        · right; have := hafterG I hI; unfold ScanLE at this; omega
        · rw [Multiset.mem_singleton] at hI; subst hI
          right; exact hFmax G hGb hGx
    · intro I hIb hIx hGI
      have hIB₂ : Multiset.count I B₂ = Multiset.count I b := by
        rw [hB₂, Multiset.count_filter_of_pos ⟨hIx, by omega⟩]
      have h1 : Multiset.count I (R : Multisegment) = 0 :=
        Multiset.count_eq_zero.mpr (fun h => by have := hRβ I h; omega)
      have h2 := hLcount I
      have h4 : List.count I L = List.count I (L.drop (P + 1)) := by
        conv_lhs => rw [hsplit]
        have ht : List.count I (L.take P) = 0 := List.count_eq_zero.mpr (fun h => by
          have := hbeforeG I h; unfold ScanLE at this; omega)
        have hs : List.count I [G] = 0 := List.count_eq_zero.mpr (fun h => by
          rw [List.mem_singleton] at h; subst h; omega)
        simp only [List.count_append, ht, hs, zero_add]
      rw [hU, Multiset.count_add, Multiset.count_add, h1, Multiset.coe_count]
      omega
  · left
    have hdrop : L.drop P = [] := List.drop_eq_nil_of_le (by omega)
    have hdrop' : (L ++ [F]).drop (P + 1) = [] :=
      List.drop_eq_nil_of_le (by simp; omega)
    rw [hdrop'] at hU
    rw [hdrop] at hU'
    simp only [Multiset.coe_nil, add_zero] at hU hU'
    refine ⟨by rw [hU]; exact fun h => hFR (Multiset.mem_coe.mp h), by rw [hU, hU'], ?_⟩
    intro I hI
    rw [hU] at hI
    exact hβ ▸ hRβ I (Multiset.mem_coe.mp hI)

/-! ### Chains below a level -/

theorem filter_erase_of_neg {s : Multisegment} (p : Interval → Prop) [DecidablePred p]
    {x : Interval} (hx : ¬ p x) : (s.erase x).filter p = s.filter p := by
  ext J
  by_cases hJ : J = x
  · subst hJ; simp [hx]
  · simp [Multiset.count_erase_of_ne hJ, Multiset.count_filter]

/-- A chain starting at most at `k` only sees the occurrences ending at most at `k`. -/
theorem chain_filter_le (k : ℤ) : ∀ (m : Multisegment) (e b : ℤ), e ≤ k →
    chain (m.filter (fun I => I.ending ≤ k)) e b =
      ((chain m e b).1, (chain m e b).2.filter (fun I => I.ending ≤ k)) := by
  intro m
  induction m using (measure (fun a : Multisegment => Multiset.card a)).wf.induction with
  | h m ih =>
  intro e b hek
  have hff : (m.filter (fun I => I.ending ≤ k)).filter
      (fun I => I.ending = e ∧ I.beginning < b) =
      m.filter (fun I => I.ending = e ∧ I.beginning < b) := by
    rw [Multiset.filter_filter]
    apply Multiset.filter_congr
    intro I _
    constructor
    · rintro ⟨h, -⟩; exact h
    · intro h; exact ⟨h, by have := h.1; omega⟩
  have hpick : pick (m.filter (fun I => I.ending ≤ k)) e b = pick m e b := by
    unfold pick; rw [hff]
  rcases hp : pick m e b with _ | I
  · rw [hp] at hpick
    rw [chain_of_pick_none hpick, chain_of_pick_none hp]
  · rw [hp] at hpick
    obtain ⟨hIe, -⟩ := pick_spec hp
    have hIm := pick_mem hp
    rw [chain_of_pick_some hpick, chain_of_pick_some hp,
      ← filter_erase_of_pos (fun I => I.ending ≤ k) (by omega : I.ending ≤ k),
      ih (m.erase I) (Multiset.card_erase_lt_of_mem hIm) (e - 1) I.beginning (by omega)]

theorem chain_fst_eq_of_filter_eq {m m' : Multisegment} {k e b : ℤ} (hek : e ≤ k)
    (h : m.filter (fun I => I.ending ≤ k) = m'.filter (fun I => I.ending ≤ k)) :
    (chain m e b).1 = (chain m' e b).1 := by
  have h1 := congrArg Prod.fst (chain_filter_le k m e b hek)
  have h2 := congrArg Prod.fst (chain_filter_le k m' e b hek)
  rw [h] at h1
  exact h1.symm.trans h2

theorem pick_eq_of_max {m : Multisegment} {e b : ℤ} {I : Interval} (hI : I ∈ m)
    (hIe : I.ending = e) (hIb : I.beginning < b)
    (hmax : ∀ J ∈ m, J.ending = e → J.beginning < b → J.beginning ≤ I.beginning) :
    pick m e b = some I := by
  rcases hp : pick m e b with _ | K
  · exfalso
    rcases (Langlands.MoeglinWaldspurger.Involution.pick_none_iff m e b).mp hp I hI with h | h <;> omega
  · obtain ⟨hKe, hKb⟩ := pick_spec hp
    have h1 := Langlands.MoeglinWaldspurger.Involution.pick_maximal hp hI hIe hIb
    have h2 := hmax K (pick_mem hp) hKe hKb
    congr 1
    exact Interval.ext (by omega) (by omega)

/-! ### Multiset identities -/

theorem cons_sub_replicate_of_ne {e p : Interval} (h : e ≠ p) (s : Multisegment) (n : ℕ) :
    (e ::ₘ s) - Multiset.replicate n p = e ::ₘ (s - Multiset.replicate n p) := by
  ext J
  by_cases hJ : J = e
  · subst hJ
    simp [Multiset.count_sub, Multiset.count_replicate, Multiset.count_cons_self, Ne.symm h]
  · simp [Multiset.count_sub, Multiset.count_replicate, Multiset.count_cons_of_ne hJ]

/-- The residual identity when the shortened input keeps the first selected occurrence. -/
theorem top_residual_identity₁ {a u u' S U : Multisegment}
    (hUa : U ≤ a) (hpart : S + u = a) (hpart' : S + u' = a - U + shorten U)
    (hSU : ∀ J ∈ S, J ∉ U) :
    u' + shorten S = u + shorten S - U + shorten U := by
  ext J
  have hle := Multiset.count_le_of_le J hUa
  have e1 := congrArg (Multiset.count J) hpart
  have e2 := congrArg (Multiset.count J) hpart'
  simp only [Multiset.count_add, Multiset.count_sub] at e1 e2 ⊢
  by_cases hs : J ∈ S
  · have h0 : Multiset.count J U = 0 := Multiset.count_eq_zero.mpr (hSU J hs)
    omega
  · have h0 : Multiset.count J S = 0 := Multiset.count_eq_zero.mpr hs
    omega

/-- The residual identity when the shortened input starts with another occurrence `G`. -/
theorem top_residual_identity₂ {a u u' S U : Multisegment} {F G : Interval} {x : ℤ}
    (hFU : F ∈ U) (hUa : U ≤ a) (hG : Multiset.count G U < Multiset.count G a)
    (hpart : {F} + S + u = a) (hpart' : {G} + S + u' = a - U + shorten U)
    (hUx : ∀ J ∈ U, J.ending = x) (hGx : G.ending = x) (hSx : ∀ J ∈ S, J.ending < x) :
    u' + shorten ({G} + S) =
      u + shorten ({F} + S) - ((U.erase F) + {G}) + shorten ((U.erase F) + {G}) := by
  have hFx : F.ending = x := hUx F hFU
  rw [shorten_erase_of_mem hFU] at hpart'
  simp only [shorten_add, shorten_singleton]
  ext J
  have hle := Multiset.count_le_of_le J hUa
  have e1 := congrArg (Multiset.count J) hpart
  have e2 := congrArg (Multiset.count J) hpart'
  have hE : Multiset.count J ({F} : Multisegment) + Multiset.count J (U.erase F) =
      Multiset.count J U := by
    rw [← Multiset.count_add, Multiset.singleton_add, Multiset.cons_erase hFU]
  have hFJ : Multiset.count J ({F} : Multisegment) ≤ Multiset.count J U := by
    rw [Multiset.count_singleton]
    split_ifs with h
    · subst h; exact Multiset.count_pos.mpr hFU
    · exact Nat.zero_le _
  have hGJ : Multiset.count J ({G} : Multisegment) + Multiset.count J U ≤
      Multiset.count J a := by
    rw [Multiset.count_singleton]
    split_ifs with h
    · subst h; omega
    · omega
  simp only [Multiset.count_add, Multiset.count_sub] at e1 e2 ⊢
  by_cases hJx : J.ending = x
  · have z1 : Multiset.count J S = 0 :=
      Multiset.count_eq_zero.mpr (fun h => by have := hSx J h; omega)
    have z2 : Multiset.count J (shorten S) = 0 := Multiset.count_eq_zero.mpr (fun h => by
      obtain ⟨K, hK, -, hJK⟩ := mem_shorten h; have := hSx K hK; omega)
    have z3 : Multiset.count J F.dropLast = 0 := Multiset.count_eq_zero.mpr (fun h => by
      have := (mem_dropLast h).2; omega)
    have z4 : Multiset.count J G.dropLast = 0 := Multiset.count_eq_zero.mpr (fun h => by
      have := (mem_dropLast h).2; omega)
    have z5 : Multiset.count J (shorten (U.erase F)) = 0 :=
      Multiset.count_eq_zero.mpr (fun h => by
        obtain ⟨K, hK, -, hJK⟩ := mem_shorten h
        have := hUx K (Multiset.mem_of_mem_erase hK); omega)
    omega
  · have z1 : Multiset.count J U = 0 := Multiset.count_eq_zero.mpr (fun h => hJx (hUx J h))
    have z2 : Multiset.count J ({F} : Multisegment) = 0 := by
      rw [Multiset.count_singleton]
      split_ifs with h
      · subst h; exact absurd hFx hJx
      · rfl
    have z3 : Multiset.count J ({G} : Multisegment) = 0 := by
      rw [Multiset.count_singleton]
      split_ifs with h
      · subst h; exact absurd hGx hJx
      · rfl
    omega

theorem cons_sub_cons' (p : Interval) (s t : Multisegment) : (p ::ₘ s) - (p ::ₘ t) = s - t := by
  ext J
  by_cases hJ : J = p
  · subst hJ; simp [Multiset.count_sub]
  · simp [Multiset.count_sub]

/-- The round of the shortened input: it starts with `first`, then selects `Δ`, then repeats
the lower selections of the original round. -/
theorem round_of_shortened {a a' : Multisegment} {x : ℤ} {F first Δ : Interval}
    {rest : List Interval}
    (hfirst : first ∈ a') (hmax : ∀ J ∈ a', J ≤ first) (hfx : first.ending = x)
    (hΔ : Δ ∈ a') (hΔx : Δ.ending = x - 1) (hΔb : Δ.beginning < first.beginning)
    (hΔmax : ∀ J ∈ a', J.ending = x - 1 → J.beginning < first.beginning →
      J.beginning ≤ Δ.beginning)
    (hlow : a'.filter (fun I => I.ending ≤ x - 2) = a.filter (fun I => I.ending ≤ x - 2))
    (hFx : F.ending = x)
    (hrest : (chain ((a.erase F).erase Δ) (x - 1 - 1) Δ.beginning).1 = rest) :
    ∃ u', round a' = some ⟨first, Δ :: rest, u'⟩ := by
  have hr := round_eq_of_max hfirst hmax
  have hne : Δ ≠ first := fun h => by rw [h] at hΔx; omega
  have hΔ' : Δ ∈ a'.erase first := (Multiset.mem_erase_of_ne hne).mpr hΔ
  have hpick : pick (a'.erase first) (first.ending - 1) first.beginning = some Δ :=
    pick_eq_of_max hΔ' (by omega) hΔb (fun J hJ hJe hJb =>
      hΔmax J (Multiset.mem_of_mem_erase hJ) (by omega) hJb)
  rw [chain_of_pick_some hpick] at hr
  have hrest' : (chain ((a'.erase first).erase Δ) (first.ending - 1 - 1) Δ.beginning).1 =
      rest := by
    rw [hfx, ← hrest]
    apply chain_fst_eq_of_filter_eq (k := x - 2) (by omega)
    rw [filter_erase_of_neg (fun I => I.ending ≤ x - 2) (show ¬ Δ.ending ≤ x - 2 by omega),
      filter_erase_of_neg (fun I => I.ending ≤ x - 2) (show ¬ first.ending ≤ x - 2 by omega),
      filter_erase_of_neg (fun I => I.ending ≤ x - 2) (show ¬ Δ.ending ≤ x - 2 by omega),
      filter_erase_of_neg (fun I => I.ending ≤ x - 2) (show ¬ F.ending ≤ x - 2 by omega),
      hlow]
  refine ⟨(chain ((a'.erase first).erase Δ) (first.ending - 1 - 1) Δ.beginning).2, ?_⟩
  rw [hr, hrest']

/-! ### The generalized top compatibility -/

theorem leftDerivative_filter_low {a : Multisegment} {x : ℤ} :
    (leftDerivative a x).filter (fun I => I.ending ≤ x - 2) =
      a.filter (fun I => I.ending ≤ x - 2) := by
  have hUe : ∀ J ∈ unmatched a x, J.ending = x := fun J hJ => mem_unmatched_ending hJ
  have g1 : (unmatched a x).filter (fun I => I.ending ≤ x - 2) = 0 :=
    Multiset.filter_eq_nil.mpr (fun J hJ hle => by have := hUe J hJ; omega)
  have g2 : (shorten (unmatched a x)).filter (fun I => I.ending ≤ x - 2) = 0 :=
    Multiset.filter_eq_nil.mpr (fun J hJ hle => by
      obtain ⟨K, hK, -, hKe⟩ := mem_shorten hJ; have := hUe K hK; omega)
  unfold leftDerivative
  rw [Multiset.filter_add, Multiset.filter_sub, g1, g2, tsub_zero, add_zero]

/-- **Generalized top compatibility.** For an input all of whose endings are at most `x`,
the output contains `[x, x]` once for each unmatched occurrence ending at `x`, and shortening
the unmatched occurrences removes exactly these points from the output. -/
theorem topCompatibility_general (x : ℤ) : ∀ (a : Multisegment), (∀ I ∈ a, I.ending ≤ x) →
    (dual a).count (point x) = (unmatched a x).card ∧
      dual (leftDerivative a x) =
        dual a - Multiset.replicate (unmatched a x).card (point x) := by
  intro a
  induction a using (measure weight).wf.induction with
  | h a ih =>
  intro hax
  rcases Classical.em (∃ I ∈ a, I.ending = x) with ⟨I₀, hI₀, hI₀x⟩ | hX
  swap
  · -- no occurrence ends at `x`
    have hX' : ∀ I ∈ a, I.ending ≠ x := fun I hI h => hX ⟨I, hI, h⟩
    have hU : unmatched a x = 0 := by
      unfold unmatched
      rw [unmatchedScan_of_ending_ne x _ 0 (fun I hI => hX' I ((Multiset.mem_sort _).mp hI))]
      rfl
    have hlow : ∀ J ∈ dual a, J.ending ≤ x - 1 :=
      dual_ending_le (fun I hI => by have := hax I hI; have := hX' I hI; omega)
    refine ⟨?_, ?_⟩
    · rw [hU, Multiset.card_zero, Multiset.count_eq_zero]
      intro h; have := hlow _ h; simp [point] at this
    · simp [leftDerivative, hU, shorten]
  obtain ⟨r, hr⟩ : ∃ r, round a = some r := by
    cases h : round a with
    | none => have := (round_none_iff a).mp h; subst this; simp at hI₀
    | some r => exact ⟨r, rfl⟩
  obtain ⟨F, t, u⟩ := r
  have hFmem : F ∈ a := Langlands.MoeglinWaldspurger.round_first_mem hr
  have hFx : F.ending = x :=
    le_antisymm (hax _ hFmem) (by have : I₀.ending ≤ F.ending := Langlands.MoeglinWaldspurger.round_ending_le_first hr hI₀; omega)
  have hdual := dual_of_round hr
  have hwt := round_weight_lt hr
  have hres_le : ∀ I ∈ Round.residual ⟨F, t, u⟩, I.ending ≤ x := fun I hI => by
    have : I.ending ≤ F.ending := round_residual_ending_le hr I hI; omega
  obtain ⟨ih1, ih2⟩ := ih _ hwt hres_le
  have hFmax : ∀ I ∈ a, I.ending = x → I.beginning ≤ F.beginning := by
    intro I hI hIx
    have hle : I ≤ F := round_first_maximal hr hI
    rcases (Langlands.MoeglinWaldspurger.Involution.interval_le_iff _ _).mp hle with h | ⟨-, h⟩
    · omega
    · exact h
  have hpart := round_partition hr
  have hchain := round_chain_eq hr
  simp only [Round.selected, Round.selectedList] at hpart hchain
  by_cases ht : t = []
  · -- one selection: the output gains `[x, x]`
    subst ht
    obtain ⟨hcard, hl1, -⟩ := chainUnmatchedCompatibility a _ hr
    have hc : (Round.emitted ⟨F, [], u⟩).beginning = x := by
      show F.ending - (([] : List Interval).length : ℤ) = x
      simp [hFx]
    have hem : Round.emitted ⟨F, [], u⟩ = point x := Interval.ext hc hFx
    rw [hc] at hcard hl1
    have hLD := hl1 rfl
    refine ⟨?_, ?_⟩
    · rw [hdual, hem, Multiset.count_cons_self, ih1, hcard]
    · rw [hLD, ih2, hdual, hem, hcard, Multiset.replicate_succ, cons_sub_cons']
  · -- several selections
    obtain ⟨Δ, rest, rfl⟩ := List.exists_cons_of_ne_nil ht
    have hpick : pick (a.erase F) (F.ending - 1) F.beginning = some Δ := by
      rcases hp : pick (a.erase F) (F.ending - 1) F.beginning with _ | K
      · rw [chain_of_pick_none hp] at hchain; simp at hchain
      · rw [chain_of_pick_some hp] at hchain
        simp only [Prod.mk.injEq, List.cons.injEq] at hchain
        rw [hchain.1.1]
    rw [chain_of_pick_some hpick] at hchain
    simp only [Prod.mk.injEq, List.cons.injEq, true_and] at hchain
    obtain ⟨hrest, -⟩ := hchain
    rw [hFx] at hrest
    have hΔm := pick_mem hpick
    obtain ⟨hΔe, hΔb⟩ := pick_spec hpick
    rw [hFx] at hΔe
    have hΔa : Δ ∈ a := Multiset.mem_of_mem_erase hΔm
    have hΔmax : ∀ I ∈ a, I.ending = x - 1 → I.beginning < F.beginning →
        I.beginning ≤ Δ.beginning := by
      intro I hI hIe hIb
      have hI' : I ∈ a.erase F := (Multiset.mem_erase_of_ne (by rintro rfl; omega)).mpr hI
      exact Langlands.MoeglinWaldspurger.Involution.pick_maximal hpick hI' (by omega) hIb
    have hrest_le : ∀ K ∈ rest, K.ending ≤ x - 2 := by
      intro K hK
      rw [← hrest] at hK
      have := chain_mem_ending_le _ _ _ hK
      omega
    -- the residual, seen at the endings `x` and `x - 1`
    simp only [Round.residual, Round.selected, Round.selectedList] at ih1 ih2 hdual
    have hresT : (u + shorten ((F :: Δ :: rest : List Interval) : Multisegment)).filter
        (TwoEnd x) = ((a.erase F).erase Δ + F.dropLast).filter (TwoEnd x) := by
      have ha : a = F ::ₘ Δ ::ₘ ((rest : Multisegment) + u) := by
        rw [← hpart, ← Multiset.cons_coe, ← Multiset.cons_coe, Multiset.cons_add,
          Multiset.cons_add]
      have hae : (a.erase F).erase Δ = (rest : Multisegment) + u := by
        rw [ha, Multiset.erase_cons_head, Multiset.erase_cons_head]
      have f1 : (rest : Multisegment).filter (TwoEnd x) = 0 :=
        Multiset.filter_eq_nil.mpr fun K hK => by
          have := hrest_le K (Multiset.mem_coe.mp hK); unfold TwoEnd; omega
      have f2 : (shorten (rest : Multisegment)).filter (TwoEnd x) = 0 :=
        Multiset.filter_eq_nil.mpr fun K hK => by
          obtain ⟨K', hK', -, hKe⟩ := mem_shorten hK
          have := hrest_le K' (Multiset.mem_coe.mp hK'); unfold TwoEnd; omega
      have f3 : Δ.dropLast.filter (TwoEnd x) = 0 :=
        Multiset.filter_eq_nil.mpr fun K hK => by
          have := (mem_dropLast hK).2; unfold TwoEnd; omega
      have f4 : F.dropLast.filter (TwoEnd x) = F.dropLast :=
        Multiset.filter_eq_self.mpr fun K hK => Or.inr (by have := (mem_dropLast hK).2; omega)
      rw [hae, ← Multiset.cons_coe, ← Multiset.cons_coe, shorten_cons, shorten_cons]
      simp only [Multiset.filter_add, f1, f2, f3, f4]
      abel
    have hUres : unmatched (u + shorten ((F :: Δ :: rest : List Interval) : Multisegment)) x =
        unmatched ((a.erase F).erase Δ + F.dropLast) x := by
      rw [← unmatched_filter, hresT, unmatched_filter]
    have hem_ne : Round.emitted ⟨F, Δ :: rest, u⟩ ≠ point x := fun h => by
      have := congrArg Interval.beginning h
      simp [Round.emitted, point] at this
      omega
    have hUe : ∀ J ∈ unmatched a x, J.ending = x := fun J hJ => mem_unmatched_ending hJ
    have hUa := unmatched_le a x
    have hcardeq : (unmatched ((a.erase F).erase Δ + F.dropLast) x).card =
        (unmatched a x).card := by
      rcases unmatched_top hFmem hFx hFmax hΔa hΔe hΔb hΔmax with
        ⟨-, h, -⟩ | ⟨hFU, G, -, -, -, -, h, -, -⟩
      · rw [h]
      · rw [h, Multiset.card_add, Multiset.card_singleton, Multiset.card_erase_add_one hFU]
    refine ⟨?_, ?_⟩
    · rw [hdual, Multiset.count_cons_of_ne (Ne.symm hem_ne), ih1, hUres, hcardeq]
    -- the shortened input
    obtain ⟨a', ha'⟩ : ∃ a', a' = leftDerivative a x := ⟨_, rfl⟩
    rw [← ha']
    have hlow : a'.filter (fun I => I.ending ≤ x - 2) = a.filter (fun I => I.ending ≤ x - 2) := by
      rw [ha']; exact leftDerivative_filter_low
    have hΔa' : Δ ∈ a' := by
      rw [ha']
      unfold leftDerivative
      refine Multiset.mem_add.mpr (Or.inl (Multiset.mem_sub.mpr ?_))
      have h0 : Multiset.count Δ (unmatched a x) = 0 :=
        Multiset.count_eq_zero.mpr (fun h => by have := hUe Δ h; omega)
      rw [h0]; exact Multiset.count_pos.mpr hΔa
    have hmem' : ∀ J ∈ a', (J ∈ a ∧ Multiset.count J (unmatched a x) < Multiset.count J a) ∨
        ∃ K ∈ unmatched a x, J.beginning = K.beginning ∧ J.ending = x - 1 := by
      intro J hJ
      rw [ha'] at hJ
      unfold leftDerivative at hJ
      rcases Multiset.mem_add.mp hJ with hJ | hJ
      · exact Or.inl ⟨Multiset.mem_of_le tsub_le_self hJ, Multiset.mem_sub.mp hJ⟩
      · obtain ⟨K, hK, hKb, hKe⟩ := mem_shorten hJ
        exact Or.inr ⟨K, hK, hKb, by rw [hKe, hUe K hK]⟩
    -- the common conclusion from a round of the shortened input
    have finish : ∀ (first : Interval) (u' : Multisegment),
        round a' = some ⟨first, Δ :: rest, u'⟩ → first.ending = x →
        u' + shorten ((first :: Δ :: rest : List Interval) : Multisegment) =
          leftDerivative (u + shorten ((F :: Δ :: rest : List Interval) : Multisegment)) x →
        dual a' = dual a - Multiset.replicate (unmatched a x).card (point x) := by
      intro first u' hr' hfx hres'
      have hem : Round.emitted ⟨first, Δ :: rest, u'⟩ = Round.emitted ⟨F, Δ :: rest, u⟩ := by
        apply Interval.ext <;> simp [Round.emitted, hfx, hFx]
      rw [dual_of_round hr', hem]
      simp only [Round.residual, Round.selected, Round.selectedList]
      rw [hres', ih2, hUres, hcardeq, hdual, cons_sub_replicate_of_ne hem_ne]
    rcases unmatched_top hFmem hFx hFmax hΔa hΔe hΔb hΔmax with
      ⟨hFU, hU', hUβ⟩ | ⟨hFU, G, hGa, hGx, hΔG, hGcount, hU', hUβG, hGtop⟩
    · -- the shortened input still starts with `F`
      have hFa' : F ∈ a' := by
        rw [ha']
        unfold leftDerivative
        refine Multiset.mem_add.mpr (Or.inl (Multiset.mem_sub.mpr ?_))
        rw [Multiset.count_eq_zero.mpr hFU]; exact Multiset.count_pos.mpr hFmem
      have hmax' : ∀ J ∈ a', J ≤ F := by
        intro J hJ
        rcases hmem' J hJ with ⟨hJa, -⟩ | ⟨K, -, -, hJe⟩
        · exact round_first_maximal hr hJa
        · exact (Langlands.MoeglinWaldspurger.Involution.interval_le_iff _ _).mpr (Or.inl (by omega))
      have hΔmax' : ∀ J ∈ a', J.ending = x - 1 → J.beginning < F.beginning →
          J.beginning ≤ Δ.beginning := by
        intro J hJ hJe hJb
        rcases hmem' J hJ with ⟨hJa, -⟩ | ⟨K, hK, hKb, -⟩
        · exact hΔmax J hJa hJe hJb
        · rw [hKb]; exact hUβ K hK
      obtain ⟨u', hr'⟩ := round_of_shortened hFa' hmax' hFx hΔa' hΔe hΔb hΔmax' hlow hFx hrest
      apply finish F u' hr' hFx
      have hpart' := round_partition hr'
      simp only [Round.selected, Round.selectedList] at hpart'
      rw [ha'] at hpart'
      unfold leftDerivative
      rw [hUres, hU']
      refine top_residual_identity₁ hUa hpart hpart' ?_
      intro J hJ hJU
      have hJx := hUe J hJU
      simp only [Multiset.mem_coe, List.mem_cons] at hJ
      rcases hJ with rfl | rfl | hJ
      · exact hFU hJU
      · omega
      · have := hrest_le J hJ; omega
    · -- the shortened input starts with the last matched occurrence `G`
      have hGa' : G ∈ a' := by
        rw [ha']
        unfold leftDerivative
        exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_sub.mpr hGcount))
      have hmax' : ∀ J ∈ a', J ≤ G := by
        intro J hJ
        rcases hmem' J hJ with ⟨hJa, hJc⟩ | ⟨K, -, -, hJe⟩
        · have hJx := hax J hJa
          rcases lt_or_eq_of_le hJx with hlt | heq
          · exact (Langlands.MoeglinWaldspurger.Involution.interval_le_iff _ _).mpr (Or.inl (by omega))
          · refine (Langlands.MoeglinWaldspurger.Involution.interval_le_iff _ _).mpr (Or.inr ⟨by omega, ?_⟩)
            by_contra hlt
            have := hGtop J hJa heq (by omega)
            omega
        · exact (Langlands.MoeglinWaldspurger.Involution.interval_le_iff _ _).mpr (Or.inl (by omega))
      have hΔmax' : ∀ J ∈ a', J.ending = x - 1 → J.beginning < G.beginning →
          J.beginning ≤ Δ.beginning := by
        intro J hJ hJe hJb
        rcases hmem' J hJ with ⟨hJa, -⟩ | ⟨K, hK, hKb, -⟩
        · exact hΔmax J hJa hJe (by have := hFmax G hGa hGx; omega)
        · rcases hUβG K hK with h | h
          · rw [hKb]; exact h
          · omega
      obtain ⟨u', hr'⟩ :=
        round_of_shortened hGa' hmax' hGx hΔa' hΔe hΔG hΔmax' hlow hFx hrest
      apply finish G u' hr' hGx
      have hpart' := round_partition hr'
      simp only [Round.selected, Round.selectedList] at hpart'
      rw [ha'] at hpart'
      unfold leftDerivative
      rw [hUres, hU']
      have hsplit : ∀ K : Interval,
          ((K :: Δ :: rest : List Interval) : Multisegment) = {K} + ((Δ :: rest : List Interval) : Multisegment) := by
        intro K; rw [← Multiset.cons_coe, Multiset.singleton_add]
      rw [hsplit] at hpart hpart' ⊢
      rw [hsplit]
      refine top_residual_identity₂ hFU hUa hGcount hpart hpart' hUe hGx ?_
      intro J hJ
      simp only [Multiset.mem_coe, List.mem_cons] at hJ
      rcases hJ with rfl | hJ
      · omega
      · have := hrest_le J hJ; omega

/-- **Proof of `TopUnmatchedCompatibility`.** -/
theorem topUnmatchedCompatibility : TopUnmatchedCompatibility := by
  intro J x hJ
  exact topCompatibility_general x J (fun I hI => by rcases hJ I hI with h | h <;> omega)

end Langlands.MoeglinWaldspurger.Derivation
