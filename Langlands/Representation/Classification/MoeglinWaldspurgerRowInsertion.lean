import Mathlib.Tactic

/-!
# Abstract row insertion with weakly decreasing rows

A row is a weakly decreasing list of integers.  Inserting `a` replaces the first
entry strictly smaller than `a` (the largest such entry) and outputs it, or appends
`a` when no entry is smaller.  This is Schensted row insertion for the reversed
order.  The main result `srl` is a single-row Knuth-type lemma comparing the words
`P ++ d :: Q ++ [e]` and `d :: (P ++ e :: Q)`.
-/

namespace Langlands.MoeglinWaldspurger.Row

/-- Weakly decreasing lists. -/
abbrev Desc (l : List ℤ) : Prop := l.Pairwise (fun x y => y ≤ x)

/-- Insert one letter into a row; the second component is the bumped entry. -/
def rIns : List ℤ → ℤ → List ℤ × Option ℤ
  | [], a => ([a], none)
  | s :: R, a => if s < a then (a :: R, some s) else (s :: (rIns R a).1, (rIns R a).2)

/-- Insert a word letter by letter, recording the bumped entry of each letter. -/
def rRun : List ℤ → List ℤ → List ℤ × List (Option ℤ)
  | R, [] => (R, [])
  | R, a :: w => ((rRun (rIns R a).1 w).1, (rIns R a).2 :: (rRun (rIns R a).1 w).2)

@[simp] theorem rIns_nil (a : ℤ) : rIns [] a = ([a], none) := rfl

theorem rIns_cons_lt {s a : ℤ} (R : List ℤ) (h : s < a) :
    rIns (s :: R) a = (a :: R, some s) := by
  simp [rIns, h]

theorem rIns_cons_ge {s a : ℤ} (R : List ℤ) (h : a ≤ s) :
    rIns (s :: R) a = (s :: (rIns R a).1, (rIns R a).2) := by
  simp [rIns, not_lt.mpr h]

@[simp] theorem rRun_nil (R : List ℤ) : rRun R [] = (R, []) := rfl

theorem rRun_cons (R : List ℤ) (a : ℤ) (w : List ℤ) :
    rRun R (a :: w) = ((rRun (rIns R a).1 w).1, (rIns R a).2 :: (rRun (rIns R a).1 w).2) :=
  rfl

theorem rRun_length (R w : List ℤ) : (rRun R w).2.length = w.length := by
  induction w generalizing R with
  | nil => simp
  | cons a w ih => simp [rRun_cons, ih]

/-- Entries at least as large as the letter are not touched. -/
theorem rIns_prefix (F R : List ℤ) (a : ℤ) (h : ∀ x ∈ F, a ≤ x) :
    rIns (F ++ R) a = (F ++ (rIns R a).1, (rIns R a).2) := by
  induction F with
  | nil => simp
  | cons s F ih =>
    simp only [List.cons_append]
    rw [rIns_cons_ge _ (h s (by simp)), ih (fun x hx => h x (by simp [hx]))]

theorem rRun_prefix (F R w : List ℤ) (h : ∀ a ∈ w, ∀ x ∈ F, a ≤ x) :
    rRun (F ++ R) w = (F ++ (rRun R w).1, (rRun R w).2) := by
  induction w generalizing R with
  | nil => simp
  | cons a w ih =>
    rw [rRun_cons, rIns_prefix F R a (h a (by simp)), ih _ (fun b hb => h b (by simp [hb])),
      rRun_cons]

theorem rRun_front (s : ℤ) (R w : List ℤ) (h : ∀ a ∈ w, a ≤ s) :
    rRun (s :: R) w = (s :: (rRun R w).1, (rRun R w).2) := by
  have := rRun_prefix [s] R w (fun a ha x hx => by simp at hx; subst hx; exact h a ha)
  simpa using this

theorem rRun_append (R w₁ w₂ : List ℤ) :
    rRun R (w₁ ++ w₂) =
      ((rRun (rRun R w₁).1 w₂).1, (rRun R w₁).2 ++ (rRun (rRun R w₁).1 w₂).2) := by
  induction w₁ generalizing R with
  | nil => simp
  | cons a w ih => simp [rRun_cons, ih]

theorem mem_rIns {R : List ℤ} {a x : ℤ} (h : x ∈ (rIns R a).1) : x ∈ R ∨ x = a := by
  induction R with
  | nil => simp at h; exact Or.inr h
  | cons s R ih =>
    by_cases hs : s < a
    · rw [rIns_cons_lt _ hs] at h
      simp only [List.mem_cons] at h
      rcases h with h | h
      · exact Or.inr h
      · exact Or.inl (List.mem_cons_of_mem _ h)
    · rw [rIns_cons_ge _ (not_lt.mp hs)] at h
      simp only [List.mem_cons] at h
      rcases h with h | h
      · exact Or.inl (h ▸ List.mem_cons_self)
      · rcases ih h with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h

theorem rIns_desc {R : List ℤ} (a : ℤ) (hR : Desc R) : Desc (rIns R a).1 := by
  induction R with
  | nil => simp
  | cons s R ih =>
    have hR' := List.pairwise_cons.mp hR
    by_cases hs : s < a
    · rw [rIns_cons_lt _ hs]
      exact List.pairwise_cons.mpr ⟨fun x hx => le_trans (hR'.1 x hx) hs.le, hR'.2⟩
    · rw [rIns_cons_ge _ (not_lt.mp hs)]
      refine List.pairwise_cons.mpr ⟨fun x hx => ?_, ih hR'.2⟩
      rcases mem_rIns hx with h | h
      · exact hR'.1 x h
      · omega

theorem rIns_none_iff (R : List ℤ) (a : ℤ) :
    (rIns R a).2 = none ↔ ∀ x ∈ R, a ≤ x := by
  induction R with
  | nil => simp
  | cons s R ih =>
    by_cases hs : s < a
    · rw [rIns_cons_lt _ hs]
      simp only [reduceCtorEq, false_iff, not_forall]
      exact ⟨s, List.mem_cons_self, not_le.mpr hs⟩
    · rw [rIns_cons_ge _ (not_lt.mp hs), ih]
      simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨fun h => ⟨not_lt.mp hs, h⟩, fun h => h.2⟩

theorem rIns_of_none {R : List ℤ} {a : ℤ} (h : ∀ x ∈ R, a ≤ x) : rIns R a = (R ++ [a], none) := by
  induction R with
  | nil => simp
  | cons s R ih =>
    rw [rIns_cons_ge _ (h s List.mem_cons_self),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    simp

/-- A bumped entry is the largest entry below the letter. -/
theorem rIns_some {R : List ℤ} {a m : ℤ} (hR : Desc R) (h : (rIns R a).2 = some m) :
    m ∈ R ∧ m < a ∧ (∀ x ∈ R, x < a → x ≤ m) ∧
      ((rIns R a).1 : Multiset ℤ) = (R : Multiset ℤ).erase m + {a} := by
  induction R with
  | nil => simp at h
  | cons s R ih =>
    have hR' := List.pairwise_cons.mp hR
    by_cases hs : s < a
    · rw [rIns_cons_lt _ hs] at h ⊢
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨List.mem_cons_self, hs, fun x hx _ => ?_, ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact le_rfl
        · exact hR'.1 x hx
      · simp
        rw [add_comm]
        rfl
    · rw [rIns_cons_ge _ (not_lt.mp hs)] at h ⊢
      obtain ⟨hm, hma, hmax, hms⟩ := ih hR'.2 h
      refine ⟨List.mem_cons_of_mem _ hm, hma, fun x hx hxa => ?_, ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · omega
        · exact hmax x hx hxa
      · have hne : s ≠ m := by omega
        rw [← Multiset.cons_coe, ← Multiset.cons_coe, hms, Multiset.erase_cons_tail_of_mem hm]
        rw [Multiset.cons_add]

/-- Inserting a letter larger than every entry of a row of small entries. -/
theorem rRun_allBelow (R L : List ℤ) (hL : Desc L) (h : ∀ x ∈ R, ∀ a ∈ L, x < a) :
    rRun R L = (L ++ R.drop L.length,
      (R.take L.length).map some ++ List.replicate (L.length - R.length) none) := by
  induction L generalizing R with
  | nil => simp
  | cons a L ih =>
    have hL' := List.pairwise_cons.mp hL
    cases R with
    | nil =>
      have := rRun_front a [] L (fun b hb => hL'.1 b hb)
      simp only [rRun_cons, rIns_nil]
      rw [this, ih [] hL'.2 (by simp)]
      simp [List.replicate_succ]
    | cons s R =>
      have hsa : s < a := h s List.mem_cons_self a List.mem_cons_self
      rw [rRun_cons, rIns_cons_lt _ hsa]
      simp only
      rw [rRun_front a R L (fun b hb => hL'.1 b hb),
        ih R hL'.2 (fun x hx b hb => h x (List.mem_cons_of_mem _ hx) b
          (List.mem_cons_of_mem _ hb))]
      simp

theorem rRun_nil_row (L : List ℤ) (hL : Desc L) :
    rRun [] L = (L, List.replicate L.length none) := by
  rw [rRun_allBelow [] L hL (by simp)]
  simp

/-- A weakly decreasing word bumps a weakly decreasing subsequence of the row, using a
prefix of its letters. -/
theorem rRun_decOuts (R w : List ℤ) (hR : Desc R) (hw : Desc w) :
    ∃ (A : List ℤ) (k : ℕ), (rRun R w).2 = A.map some ++ List.replicate k none ∧
      A.Sublist R := by
  induction R generalizing w with
  | nil => exact ⟨[], w.length, by simp [rRun_nil_row w hw], List.Sublist.slnil⟩
  | cons s R ih =>
    have hR' := List.pairwise_cons.mp hR
    cases w with
    | nil => exact ⟨[], 0, by simp, List.nil_sublist _⟩
    | cons a w =>
      have hw' := List.pairwise_cons.mp hw
      by_cases hs : s < a
      · rw [rRun_cons, rIns_cons_lt _ hs]
        simp only
        rw [rRun_front a R w (fun b hb => hw'.1 b hb)]
        obtain ⟨A, k, hA, hsub⟩ := ih w hR'.2 hw'.2
        exact ⟨s :: A, k, by simp [hA], hsub.cons_cons s⟩
      · have hall : ∀ b ∈ a :: w, b ≤ s := by
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · omega
          · exact le_trans (hw'.1 b hb) (by omega)
        rw [rRun_front s R (a :: w) hall]
        obtain ⟨A, k, hA, hsub⟩ := ih (a :: w) hR'.2 hw
        exact ⟨A, k, hA, hsub.cons s⟩

/-! ## The single-row lemma -/

/-- A Knuth pair: `P ++ d :: Q` is weakly decreasing, `P ≥ e > d`. -/
def KP (P : List ℤ) (d : ℤ) (Q : List ℤ) (e : ℤ) : Prop :=
  Desc (P ++ d :: Q) ∧ (∀ x ∈ P, e ≤ x) ∧ d < e

/-- The shape of the bumped words in the single-row lemma: either both processes bump
the same word (`EQ`), or the bumped words again form a Knuth pair (`RW`). -/
def SRLOut (R : List ℤ) (d : ℤ) (oY oX : List (Option ℤ)) : Prop :=
  ∃ (A : List ℤ) (ε : ℤ) (k : ℕ), oY = A.map some ++ List.replicate k none ++ [some ε] ∧
    (∀ x ∈ A, x ∈ R) ∧ (ε ∈ R ∨ ε = d) ∧
    ((0 < k ∧ Desc (A ++ [ε]) ∧
        oX = none :: ((A ++ [ε]).map some ++ List.replicate (k - 1) none)) ∨
     (R ≠ [] ∧ ∃ (A₁ : List ℤ) (a : ℤ) (A₂ : List ℤ), A = A₁ ++ a :: A₂ ∧ KP A₁ a A₂ ε ∧
        oX = some a :: ((A₁ ++ ε :: A₂).map some ++ List.replicate k none)))

theorem SRLOut.mono {R R' : List ℤ} {d : ℤ} {oY oX : List (Option ℤ)}
    (hsub : ∀ x ∈ R', x ∈ R) (hne : R ≠ []) (h : SRLOut R' d oY oX) : SRLOut R d oY oX := by
  obtain ⟨A, ε, k, hY, hA, hε, hX⟩ := h
  refine ⟨A, ε, k, hY, fun x hx => hsub x (hA x hx), ?_, ?_⟩
  · rcases hε with h | h
    · exact Or.inl (hsub _ h)
    · exact Or.inr h
  · rcases hX with h | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨hne, h⟩

theorem SRLOut.cons_hi {R : List ℤ} {s d : ℤ} {o : Option ℤ} {oY oW : List (Option ℤ)}
    (hds : d ≤ s) (hR : ∀ x ∈ R, x ≤ s) (h : SRLOut R d oY (o :: oW)) :
    SRLOut (s :: R) d (some s :: oY) (o :: some s :: oW) := by
  obtain ⟨A, ε, k, hY, hA, hε, hX⟩ := h
  have hεs : ε ≤ s := by
    rcases hε with h | h
    · exact hR ε h
    · omega
  have hAs : ∀ x ∈ A, x ≤ s := fun x hx => hR x (hA x hx)
  refine ⟨s :: A, ε, k, by simp [hY], ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hA x hx)
  · rcases hε with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · exact Or.inr h
  · rcases hX with ⟨hk, hdesc, hX⟩ | ⟨_, A₁, a, A₂, hAeq, hKP, hX⟩
    · simp only [List.cons.injEq] at hX
      obtain ⟨rfl, rfl⟩ := hX
      refine Or.inl ⟨hk, ?_, by simp⟩
      rw [List.cons_append]
      refine List.pairwise_cons.mpr ⟨fun x hx => ?_, hdesc⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact hAs x hx
      · rw [List.mem_singleton.mp hx]; exact hεs
    · simp only [List.cons.injEq] at hX
      obtain ⟨rfl, rfl⟩ := hX
      refine Or.inr ⟨List.cons_ne_nil _ _, s :: A₁, a, A₂, by simp [hAeq], ?_, by simp⟩
      obtain ⟨hd, hP, hlt⟩ := hKP
      refine ⟨?_, ?_, hlt⟩
      · rw [List.cons_append]
        refine List.pairwise_cons.mpr ⟨fun x hx => ?_, hd⟩
        exact hAs x (by rw [hAeq]; exact hx)
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hεs
        · exact hP x hx

theorem KP.desc_P {P Q : List ℤ} {d e : ℤ} (h : KP P d Q e) : Desc P :=
  (List.pairwise_append.mp h.1).1

theorem KP.desc_dQ {P Q : List ℤ} {d e : ℤ} (h : KP P d Q e) : Desc (d :: Q) :=
  (List.pairwise_append.mp h.1).2.1

theorem KP.P_ge_d {P Q : List ℤ} {d e : ℤ} (h : KP P d Q e) : ∀ x ∈ P, ∀ y ∈ d :: Q, y ≤ x :=
  (List.pairwise_append.mp h.1).2.2

theorem KP.Q_le_d {P Q : List ℤ} {d e : ℤ} (h : KP P d Q e) : ∀ y ∈ Q, y ≤ d :=
  fun y hy => (List.pairwise_cons.mp h.desc_dQ).1 y hy

theorem KP.desc_Pd {P Q : List ℤ} {d e : ℤ} (h : KP P d Q e) : Desc (P ++ [d]) := by
  refine List.pairwise_append.mpr ⟨h.desc_P, by simp, fun x hx y hy => ?_⟩
  simp at hy; subst hy; exact h.P_ge_d x hx _ List.mem_cons_self

theorem KP.desc_Pe {P Q : List ℤ} {d e : ℤ} (h : KP P d Q e) : Desc (P ++ [e]) := by
  refine List.pairwise_append.mpr ⟨h.desc_P, by simp, fun x hx y hy => ?_⟩
  simp at hy; subst hy; exact h.2.1 x hx

theorem KP.desc_Q {P Q : List ℤ} {d e : ℤ} (h : KP P d Q e) : Desc Q :=
  (List.pairwise_cons.mp h.desc_dQ).2

theorem KP.tail {p d e : ℤ} {P Q : List ℤ} (h : KP (p :: P) d Q e) : KP P d Q e :=
  ⟨(List.pairwise_cons.mp h.1).2, fun x hx => h.2.1 x (List.mem_cons_of_mem _ hx), h.2.2⟩

/-- Base case: every entry of the row is below `d`. -/
theorem srl_base (R P Q : List ℤ) (d e : ℤ) (hR : Desc R) (hKP : KP P d Q e)
    (hlow : ∀ x ∈ R, x < d) :
    (rRun R (P ++ d :: Q ++ [e])).1 = (rRun R (d :: (P ++ e :: Q))).1 ∧
    SRLOut R d (rRun R (P ++ d :: Q ++ [e])).2 (rRun R (d :: (P ++ e :: Q))).2 := by
  set j := P.length + 1 with hj
  have hPd := hKP.desc_Pd
  have hPe := hKP.desc_Pe
  have hQd := hKP.Q_le_d
  have hPge := hKP.P_ge_d
  have hdP : ∀ x ∈ P, d ≤ x := fun x hx => hPge x hx d List.mem_cons_self
  have hde := hKP.2.2
  have heP := hKP.2.1
  -- the Y process
  have hY1 : rRun R (P ++ [d]) = ((P ++ [d]) ++ R.drop j,
      (R.take j).map some ++ List.replicate (j - R.length) none) := by
    rw [rRun_allBelow R (P ++ [d]) hPd]
    · simp [hj]
    · intro x hx a ha
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact lt_of_lt_of_le (hlow x hx) (hdP a ha)
      · exact hlow x hx
  set T := (rRun (R.drop j) Q).1 with hT
  set oQ := (rRun (R.drop j) Q).2 with hoQ
  have hY2 : rRun ((P ++ [d]) ++ R.drop j) Q = ((P ++ [d]) ++ T, oQ) := by
    rw [rRun_prefix]
    intro a ha x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact le_trans (hQd a ha) (hdP x hx)
    · exact hQd a ha
  have hY3 : rIns ((P ++ [d]) ++ T) e = (P ++ e :: T, some d) := by
    rw [List.append_assoc, List.singleton_append, rIns_prefix P _ e heP, rIns_cons_lt _ hde]
  have hY : rRun R (P ++ d :: Q ++ [e]) = (P ++ e :: T,
      (R.take j).map some ++ List.replicate (j - R.length) none ++ oQ ++ [some d]) := by
    have : P ++ d :: Q ++ [e] = (P ++ [d]) ++ (Q ++ [e]) := by simp
    rw [this, rRun_append, hY1, rRun_append, hY2]
    simp only
    rw [rRun_cons, hY3]
    simp
  -- the X process
  have hrow : ∀ (row : List ℤ), row.drop (j - 1) = R.drop j → (∀ x ∈ row, x ≤ d) →
      rRun (d :: row) (P ++ e :: Q) = (P ++ e :: T,
        ((d :: row).take j).map some ++ List.replicate (j - (row.length + 1)) none ++ oQ) := by
    intro row hdrop hle
    have hW : P ++ e :: Q = (P ++ [e]) ++ Q := by simp
    rw [hW, rRun_append, rRun_allBelow (d :: row) (P ++ [e]) hPe]
    · simp only
      rw [rRun_prefix]
      · have : (d :: row).drop (P ++ [e]).length = R.drop j := by
          simp only [List.length_append, List.length_singleton, List.drop_succ_cons]
          exact hdrop
        rw [this, ← hT, ← hoQ]
        simp [hj]
      · intro a ha x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact le_trans (hQd a ha) (hdP x hx)
        · rw [List.mem_singleton.mp hx]; exact le_trans (hQd a ha) hde.le
    · intro x hx a ha
      have hxd : x < e := by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hde
        · exact lt_of_le_of_lt (hle x hx) hde
      rcases List.mem_append.mp ha with ha | ha
      · exact lt_of_lt_of_le hxd (heP a ha)
      · rw [List.mem_singleton.mp ha]; exact hxd
  obtain ⟨B, kQ, hB, hBsub⟩ := rRun_decOuts (R.drop j) Q (hR.sublist (List.drop_sublist _ _))
    hKP.desc_Q
  rw [← hoQ] at hB
  rw [hY]
  cases R with
  | nil =>
    have hX : rRun [] (d :: (P ++ e :: Q)) =
        (P ++ e :: T, none :: some d :: (List.replicate (j - 1) none ++ oQ)) := by
      rw [rRun_cons, rIns_nil]
      simp only
      rw [hrow [] (by simp) (by simp)]
      rw [List.take_of_length_le (by simp [hj])]
      simp
    rw [hX]
    refine ⟨rfl, ?_⟩
    have hBnil : B = [] := by simpa using hBsub
    subst hBnil
    refine ⟨[], d, j + kQ, ?_, by simp, Or.inr rfl, Or.inl ⟨by omega, by simp, ?_⟩⟩
    · rw [hB]
      simp only [List.take_nil, List.map_nil, List.nil_append, List.length_nil, Nat.sub_zero,
        List.replicate_add, List.append_assoc]
    · rw [hB]
      have : j + kQ - 1 = (j - 1) + kQ := by omega
      rw [this]
      simp only [List.map_nil, List.nil_append, List.replicate_add, List.map_cons,
        List.cons_append]
  | cons s R' =>
    have hsd : s < d := hlow s List.mem_cons_self
    have hX : rRun (s :: R') (d :: (P ++ e :: Q)) =
        (P ++ e :: T, some s :: (((d :: R').take j).map some ++
          List.replicate (j - (R'.length + 1)) none ++ oQ)) := by
      rw [rRun_cons, rIns_cons_lt _ hsd]
      simp only
      rw [hrow R' (by simp [hj]) (fun x hx => (hlow x (List.mem_cons_of_mem _ hx)).le)]
    rw [hX]
    refine ⟨rfl, ?_⟩
    obtain ⟨j', hj'⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have htake : ∀ x : ℤ, (x :: R').take j = x :: R'.take (j - 1) := by
      intro x; rw [hj']; simp
    have hdropj : (s :: R').drop j = R'.drop (j - 1) := by rw [hj']; simp
    have hswap : List.replicate (j - (R'.length + 1)) none ++ B.map some =
        B.map some ++ List.replicate (j - (R'.length + 1)) (none : Option ℤ) := by
      by_cases hle : j ≤ R'.length + 1
      · have : j - (R'.length + 1) = 0 := by omega
        rw [this]; simp
      · have : (s :: R').drop j = [] := List.drop_eq_nil_of_le (by simp; omega)
        rw [this] at hBsub
        have : B = [] := by simpa using hBsub
        subst this; simp
    have hsubR : (R'.take (j - 1) ++ B).Sublist R' := by
      have h1 : B.Sublist (R'.drop (j - 1)) := hdropj ▸ hBsub
      have := (List.Sublist.refl (R'.take (j - 1))).append h1
      rwa [List.take_append_drop] at this
    refine ⟨s :: (R'.take (j - 1) ++ B), d, j - (R'.length + 1) + kQ, ?_, ?_, Or.inr rfl,
      Or.inr ⟨List.cons_ne_nil _ _, [], s, R'.take (j - 1) ++ B, by simp, ?_, ?_⟩⟩
    · rw [hB, htake s]
      simp only [List.length_cons, List.map_cons, List.map_append, List.replicate_add,
        List.cons_append, List.append_assoc]
      rw [← List.append_assoc (List.replicate _ none) (B.map some), hswap]
      simp
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hsubR.subset hx)
    · refine ⟨?_, by simp, hsd⟩
      simp only [List.nil_append]
      exact hR.sublist (hsubR.cons_cons s)
    · rw [hB, htake d]
      simp only [List.map_cons, List.map_append, List.replicate_add, List.nil_append,
        List.cons_append, List.append_assoc]
      rw [← List.append_assoc (List.replicate _ none) (B.map some), hswap]
      simp

/-- The single-row lemma. -/
theorem srl (R P Q : List ℤ) (d e : ℤ) (hR : Desc R) (hKP : KP P d Q e) :
    (rRun R (P ++ d :: Q ++ [e])).1 = (rRun R (d :: (P ++ e :: Q))).1 ∧
    SRLOut R d (rRun R (P ++ d :: Q ++ [e])).2 (rRun R (d :: (P ++ e :: Q))).2 := by
  induction R generalizing P with
  | nil => exact srl_base [] P Q d e hR hKP (by simp)
  | cons s R ih =>
    have hR' := List.pairwise_cons.mp hR
    by_cases hsd : s < d
    · exact srl_base (s :: R) P Q d e hR hKP (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hsd
        · exact lt_of_le_of_lt (hR'.1 x hx) hsd)
    have hds : d ≤ s := not_lt.mp hsd
    have hQd := hKP.Q_le_d
    have hde := hKP.2.2
    -- case (α): `s` is inert for every letter
    have halpha : (∀ x ∈ P, x ≤ s) → e ≤ s →
        (rRun (s :: R) (P ++ d :: Q ++ [e])).1 = (rRun (s :: R) (d :: (P ++ e :: Q))).1 ∧
        SRLOut (s :: R) d (rRun (s :: R) (P ++ d :: Q ++ [e])).2
          (rRun (s :: R) (d :: (P ++ e :: Q))).2 := by
      intro hP hes
      have hY : ∀ a ∈ P ++ d :: Q ++ [e], a ≤ s := by
        intro a ha
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with (ha | rfl | ha) | rfl
        · exact hP a ha
        · exact hds
        · exact le_trans (hQd a ha) hds
        · exact hes
      have hX : ∀ a ∈ d :: (P ++ e :: Q), a ≤ s := by
        intro a ha
        simp only [List.mem_append, List.mem_cons] at ha
        rcases ha with rfl | ha | rfl | ha
        · exact hds
        · exact hP a ha
        · exact hes
        · exact le_trans (hQd a ha) hds
      rw [rRun_front s R _ hY, rRun_front s R _ hX]
      obtain ⟨h1, h2⟩ := ih P hR'.2 hKP
      exact ⟨by rw [h1], h2.mono (fun x hx => List.mem_cons_of_mem _ hx) (List.cons_ne_nil _ _)⟩
    cases P with
    | nil =>
      by_cases hes : e ≤ s
      · exact halpha (by simp) hes
      -- case (γ): `P = []` and `d ≤ s < e`
      have hse : s < e := not_le.mp hes
      have hdQ : ∀ a ∈ d :: Q, a ≤ s := by
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hds
        · exact le_trans (hQd a ha) hds
      set R₁ := (rIns R d).1
      set od := (rIns R d).2 with hod
      have hRd : rRun R (d :: Q) = ((rRun R₁ Q).1, od :: (rRun R₁ Q).2) := rRun_cons R d Q
      have hY : rRun (s :: R) ([] ++ d :: Q ++ [e]) =
          (e :: (rRun R₁ Q).1, od :: (rRun R₁ Q).2 ++ [some s]) := by
        have : [] ++ d :: Q ++ [e] = (d :: Q) ++ [e] := by simp
        rw [this, rRun_append, rRun_front s R _ hdQ, hRd]
        simp only
        rw [rRun_cons, rIns_cons_lt _ hse]
        simp
      have hX : rRun (s :: R) (d :: ([] ++ e :: Q)) =
          (e :: (rRun R₁ Q).1, od :: some s :: (rRun R₁ Q).2) := by
        simp only [List.nil_append]
        rw [rRun_cons, rIns_cons_ge _ hds]
        simp only
        rw [rRun_cons, rIns_cons_lt _ hse]
        simp only
        rw [rRun_front e R₁ Q (fun a ha => le_trans (hQd a ha) hde.le)]
      rw [hY, hX]
      refine ⟨rfl, ?_⟩
      simp only
      obtain ⟨B, k, hB, hBsub⟩ := rRun_decOuts R (d :: Q) hR'.2 hKP.desc_dQ
      rw [hRd] at hB
      simp only at hB
      have hlen : (B.map some ++ List.replicate k (none : Option ℤ)).length = Q.length + 1 := by
        rw [← hB]; simp [rRun_length]
      cases B with
      | nil =>
        simp only [List.map_nil, List.nil_append, List.length_replicate] at hB hlen
        subst hlen
        simp only [List.replicate_succ, List.cons.injEq] at hB
        obtain ⟨hod', hQ⟩ := hB
        refine ⟨[], s, Q.length + 1, ?_, by simp, Or.inl List.mem_cons_self,
          Or.inl ⟨by omega, by simp, ?_⟩⟩
        · rw [hod', hQ]; simp [List.replicate_succ]
        · rw [hod', hQ]; simp
      | cons a B =>
        simp only [List.map_cons, List.cons_append, List.cons.injEq] at hB
        obtain ⟨hod', hQ⟩ := hB
        have had : a < d := (rIns_some (R := R) (a := d) (m := a) hR'.2 hod').2.1
        have hsubR : (a :: B).Sublist R := hBsub
        refine ⟨a :: B, s, k, ?_, ?_, Or.inl List.mem_cons_self,
          Or.inr ⟨List.cons_ne_nil _ _, [], a, B, by simp, ⟨?_, by simp, by omega⟩, ?_⟩⟩
        · rw [hod', hQ]; simp
        · intro x hx; exact List.mem_cons_of_mem _ (hsubR.subset hx)
        · simpa using hR'.2.sublist hsubR
        · rw [hod', hQ]; simp
    | cons p P =>
      by_cases hps : p ≤ s
      · have hP : ∀ x ∈ p :: P, x ≤ s := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hps
          · exact le_trans ((List.pairwise_cons.mp hKP.desc_P).1 x hx) hps
        exact halpha hP (le_trans (hKP.2.1 p List.mem_cons_self) hps)
      -- case (β): `d ≤ s < p`
      have hsp : s < p := not_le.mp hps
      have hKP' := hKP.tail
      have hpge : ∀ a ∈ P ++ d :: Q ++ [e], a ≤ p := by
        intro a ha
        have hPd := hKP.P_ge_d p List.mem_cons_self
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with (ha | rfl | ha) | rfl
        · exact (List.pairwise_cons.mp hKP.desc_P).1 a ha
        · exact hPd a List.mem_cons_self
        · exact hPd a (List.mem_cons_of_mem _ ha)
        · exact hKP.2.1 p List.mem_cons_self
      have hpgeW : ∀ a ∈ P ++ e :: Q, a ≤ p := by
        intro a ha
        apply hpge
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
        tauto
      set R₁ := (rIns R d).1
      set od := (rIns R d).2
      have hY : rRun (s :: R) ((p :: P) ++ d :: Q ++ [e]) =
          (p :: (rRun R (P ++ d :: Q ++ [e])).1, some s :: (rRun R (P ++ d :: Q ++ [e])).2) := by
        simp only [List.cons_append]
        rw [rRun_cons, rIns_cons_lt _ hsp]
        simp only
        rw [rRun_front p R _ hpge]
      have hX : rRun (s :: R) (d :: ((p :: P) ++ e :: Q)) =
          (p :: (rRun R₁ (P ++ e :: Q)).1, od :: some s :: (rRun R₁ (P ++ e :: Q)).2) := by
        rw [rRun_cons, rIns_cons_ge _ hds]
        simp only [List.cons_append]
        rw [rRun_cons, rIns_cons_lt _ hsp]
        simp only
        rw [rRun_front p R₁ _ hpgeW]
      have hX' : rRun R (d :: (P ++ e :: Q)) =
          ((rRun R₁ (P ++ e :: Q)).1, od :: (rRun R₁ (P ++ e :: Q)).2) := rRun_cons _ _ _
      obtain ⟨h1, h2⟩ := ih P hR'.2 hKP'
      rw [hX'] at h1 h2
      rw [hY, hX]
      exact ⟨by simp only at h1 ⊢; rw [h1], h2.cons_hi hds hR'.1⟩

end Langlands.MoeglinWaldspurger.Row
