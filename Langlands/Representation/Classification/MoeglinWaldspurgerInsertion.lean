import Langlands.Representation.Classification.MoeglinWaldspurger
import Langlands.Representation.Classification.MoeglinWaldspurgerRowInsertion

/-!
# The Moeglin–Waldspurger round as a row insertion

Row `g` of a multisegment is the multiset of beginnings of its intervals ending
at `g`.  The chain of one MW round is a row insertion: `insR a g v` bumps the
largest beginning `< v` at row `g`, shortens that interval, carries its beginning
to row `g - 1`, and finally adds `[v, g]` when `v ≤ g`.  The main results are the
bridge `dual a = emit e n + dual (insR a e (e+1)).1` and row processing `rowProc`.
-/

namespace Langlands.MoeglinWaldspurger.Involution

open Row (Desc)

/-! ## The selection `pick` -/

theorem interval_le_iff (I J : Interval) :
    I ≤ J ↔ I.ending < J.ending ∨ I.ending = J.ending ∧ I.beginning ≤ J.beginning := by
  change toLex (I.ending, I.beginning) ≤ toLex (J.ending, J.beginning) ↔ _
  exact Prod.Lex.toLex_le_toLex

/-- The selection maximizes the beginning among admissible intervals. -/
theorem pick_maximal {a : Multisegment} {e b : ℤ} {I : Interval}
    (h : pick a e b = some I) {J : Interval} (hJ : J ∈ a)
    (he : J.ending = e) (hb : J.beginning < b) :
    J.beginning ≤ I.beginning := by
  have hs := Multiset.pairwise_sort (a.filter fun K => K.ending = e ∧ K.beginning < b)
    (fun K L : Interval => L ≤ K)
  have hm : J ∈ (a.filter fun K => K.ending = e ∧ K.beginning < b).sort
      (fun K L : Interval => L ≤ K) := by
    exact (Multiset.mem_sort _).mpr (Multiset.mem_filter.mpr ⟨hJ, he, hb⟩)
  unfold pick at h
  cases hl : (a.filter fun K => K.ending = e ∧ K.beginning < b).sort
      (fun K L : Interval => L ≤ K) with
  | nil => simp [hl] at h
  | cons K l =>
    simp only [hl, List.head?_cons, Option.some.injEq] at h
    subst K
    rw [hl] at hs hm
    have hle : J ≤ I := by
      rcases List.mem_cons.mp hm with rfl | hm
      · exact le_rfl
      · exact (List.pairwise_cons.mp hs).1 _ hm
    have hIe := (pick_spec (show pick a e b = some I from by simp [pick, hl])).1
    rcases (interval_le_iff _ _).mp hle with hlt | ⟨_, hbeg⟩
    · omega
    · exact hbeg

theorem pick_none_iff (a : Multisegment) (e b : ℤ) :
    pick a e b = none ↔ ∀ I ∈ a, I.ending ≠ e ∨ b ≤ I.beginning := by
  unfold pick
  rw [List.head?_eq_none_iff]
  constructor
  · intro h I hI
    have hf : a.filter (fun I => I.ending = e ∧ I.beginning < b) = 0 := by
      have := Multiset.sort_eq (a.filter fun I => I.ending = e ∧ I.beginning < b)
        (fun I J : Interval => J ≤ I)
      simpa [h] using this.symm
    by_contra hn
    have he : I.ending = e := by tauto
    have hb : I.beginning < b := by omega
    have hm : I ∈ a.filter (fun I => I.ending = e ∧ I.beginning < b) :=
      Multiset.mem_filter.mpr ⟨hI, he, hb⟩
    rw [hf] at hm
    exact Multiset.notMem_zero I hm
  · intro h
    have hf : a.filter (fun I => I.ending = e ∧ I.beginning < b) = 0 := by
      apply Multiset.eq_zero_of_forall_notMem
      intro I hI
      obtain ⟨hIa, he, hb⟩ := Multiset.mem_filter.mp hI
      rcases h I hIa with hn | hn <;> omega
    simp [hf]

/-- An admissible interval is picked exactly when it has maximal beginning. -/
theorem pick_eq_some_iff (a : Multisegment) (e b : ℤ) (I : Interval) :
    pick a e b = some I ↔ I ∈ a ∧ I.ending = e ∧ I.beginning < b ∧
      ∀ J ∈ a, J.ending = e → J.beginning < b → J.beginning ≤ I.beginning := by
  constructor
  · intro h
    exact ⟨pick_mem h, (pick_spec h).1, (pick_spec h).2, fun _ hm he hb =>
      pick_maximal h hm he hb⟩
  · rintro ⟨hIa, hIe, hIb, hmax⟩
    cases hp : pick a e b with
    | none =>
      rcases (pick_none_iff a e b).mp hp I hIa with h | h <;> omega
    | some J =>
      have hJ := pick_spec hp
      have hle := hmax J (pick_mem hp) hJ.1 hJ.2
      have hge := pick_maximal hp hIa hIe hIb
      have hJI : J = I := Interval.ext (by omega) (by omega)
      subst hJI
      rfl

/-! ## Single intervals and rows placed at a fixed ending -/

/-- The interval `[b, g]` as a multisegment, or `0` when `g < b`. -/
def seg (b g : ℤ) : Multisegment := if h : b ≤ g then {⟨b, g, h⟩} else 0

theorem seg_of_le {b g : ℤ} (h : b ≤ g) : seg b g = {⟨b, g, h⟩} := by simp [seg, h]

theorem seg_of_lt {b g : ℤ} (h : g < b) : seg b g = 0 := by simp [seg, not_le.mpr h]

theorem mem_seg {b g : ℤ} {J : Interval} : J ∈ seg b g ↔ J.beginning = b ∧ J.ending = g := by
  unfold seg
  split_ifs with h
  · simp only [Multiset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h2⟩
      exact Interval.ext h1 h2
  · simp only [Multiset.notMem_zero, false_iff]
    rintro ⟨h1, h2⟩
    have := J.nonempty
    omega

theorem seg_self (I : Interval) : seg I.beginning I.ending = {I} := by
  rw [seg_of_le I.nonempty]

theorem dropLast_eq (I : Interval) : I.dropLast = seg I.beginning (I.ending - 1) := by
  unfold Interval.dropLast seg
  split_ifs <;> first | rfl | omega

theorem weight_seg (b g : ℤ) : weight (seg b g) = (g + 1 - b).toNat := by
  unfold seg
  split_ifs with h
  · simp [weight, Interval.length]
    omega
  · simp
    omega

/-- The emitted interval `[e+1-n, e]` (nothing when `n = 0`). -/
def emit (e : ℤ) (n : ℕ) : Multisegment := seg (e + 1 - n) e

/-- Intervals `[b, g]` for the beginnings `b ∈ M`; beginnings above `g` are dropped. -/
def place (M : Multiset ℤ) (g : ℤ) : Multisegment := M.bind fun b => seg b g

@[simp] theorem place_zero (g : ℤ) : place 0 g = 0 := Multiset.zero_bind _

theorem place_add (M N : Multiset ℤ) (g : ℤ) : place (M + N) g = place M g + place N g :=
  Multiset.add_bind _ _ _

theorem place_cons (b : ℤ) (M : Multiset ℤ) (g : ℤ) :
    place (b ::ₘ M) g = seg b g + place M g :=
  Multiset.cons_bind _ _ _

theorem place_singleton (b g : ℤ) : place {b} g = seg b g := Multiset.singleton_bind _ _

theorem mem_place {M : Multiset ℤ} {g : ℤ} {J : Interval} :
    J ∈ place M g ↔ J.beginning ∈ M ∧ J.ending = g := by
  simp only [place, Multiset.mem_bind, mem_seg]
  constructor
  · rintro ⟨b, hb, h1, h2⟩
    exact ⟨h1 ▸ hb, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨_, h1, rfl, h2⟩

theorem place_erase {M : Multiset ℤ} {m g : ℤ} (hm : m ∈ M) (hmg : m ≤ g) :
    (place M g).erase ⟨m, g, hmg⟩ = place (M.erase m) g := by
  conv_lhs => rw [← Multiset.cons_erase hm]
  rw [place_cons, seg_of_le hmg, Multiset.singleton_add, Multiset.erase_cons_head]

theorem shorten_zero : shorten 0 = 0 := Multiset.zero_bind _

theorem shorten_add (s t : Multisegment) : shorten (s + t) = shorten s + shorten t :=
  Multiset.add_bind _ _ _

theorem shorten_cons (I : Interval) (s : Multisegment) :
    shorten (I ::ₘ s) = I.dropLast + shorten s :=
  Multiset.cons_bind _ _ _

theorem mem_shorten {s : Multisegment} {J : Interval} (h : J ∈ shorten s) :
    ∃ I ∈ s, J.beginning = I.beginning ∧ J.ending = I.ending - 1 := by
  obtain ⟨I, hI, hJ⟩ := Multiset.mem_bind.mp h
  rw [dropLast_eq, mem_seg] at hJ
  exact ⟨I, hI, hJ⟩

theorem weight_erase {a : Multisegment} {I : Interval} (h : I ∈ a) :
    weight (a.erase I) + I.length = weight a := by
  conv_rhs => rw [← Multiset.cons_erase h]
  rw [weight_cons]
  omega

/-! ## The chain as a row insertion -/

theorem chain_of_pick_none {a : Multisegment} {g v : ℤ} (h : pick a g v = none) :
    chain a g v = ([], a) := by
  rw [chain]
  split
  · rfl
  · rename_i I hp
    rw [h] at hp
    cases hp

theorem chain_of_pick_some {a : Multisegment} {g v : ℤ} {I : Interval}
    (h : pick a g v = some I) :
    chain a g v = (I :: (chain (a.erase I) (g - 1) I.beginning).1,
      (chain (a.erase I) (g - 1) I.beginning).2) := by
  rw [chain]
  split
  · rename_i hp
    rw [h] at hp
    cases hp
  · rename_i J hp
    rw [h] at hp
    cases hp
    rfl

/-- Row insertion of `v` at row `g`: the untouched intervals, the shortened chain,
the new interval `[v, g]` if `v ≤ g`, and the number of bumps. -/
def insR (a : Multisegment) (g v : ℤ) : Multisegment × ℕ :=
  ((chain a g v).2 + shorten ((chain a g v).1 : Multisegment) + seg v g,
    (chain a g v).1.length)

theorem insR_of_pick_none {a : Multisegment} {g v : ℤ} (h : pick a g v = none) :
    insR a g v = (a + seg v g, 0) := by
  simp [insR, chain_of_pick_none h, shorten_zero]

theorem insR_of_pick_some {a : Multisegment} {g v : ℤ} {I : Interval}
    (h : pick a g v = some I) :
    insR a g v = ((insR (a.erase I) (g - 1) I.beginning).1 + seg v g,
      (insR (a.erase I) (g - 1) I.beginning).2 + 1) := by
  have hI := (pick_spec h).1
  simp only [insR, chain_of_pick_some h, List.length_cons, ← Multiset.cons_coe, shorten_cons,
    dropLast_eq, hI]
  congr 1
  abel

theorem pick_add_high {h z : Multisegment} {g v : ℤ} (hh : ∀ J ∈ h, g < J.ending) :
    pick (h + z) g v = pick z g v := by
  unfold pick
  rw [Multiset.filter_add, Multiset.filter_eq_nil.mpr (fun J hJ hJ' => by
    have := hh J hJ
    have := hJ'.1
    omega), zero_add]

theorem chain_add_high (h z : Multisegment) : ∀ g v : ℤ, (∀ J ∈ h, g < J.ending) →
    chain (h + z) g v = ((chain z g v).1, (chain z g v).2 + h) := by
  induction z using (measure (fun a : Multisegment => a.card)).wf.induction with
  | h z ih =>
    intro g v hh
    cases hp : pick z g v with
    | none =>
      have hp' : pick (h + z) g v = none := by rw [pick_add_high hh, hp]
      rw [chain_of_pick_none hp', chain_of_pick_none hp, add_comm]
    | some I =>
      have hp' : pick (h + z) g v = some I := by rw [pick_add_high hh, hp]
      have hI := pick_mem hp
      rw [chain_of_pick_some hp', chain_of_pick_some hp, Multiset.erase_add_right_pos h hI,
        ih (z.erase I) (Multiset.card_erase_lt_of_mem hI) (g - 1) I.beginning
          (fun J hJ => by have := hh J hJ; omega)]

/-- Intervals ending above the insertion row are inert. -/
theorem insR_add_high {h : Multisegment} (z : Multisegment) {g : ℤ} (v : ℤ)
    (hh : ∀ J ∈ h, g < J.ending) :
    insR (h + z) g v = ((insR z g v).1 + h, (insR z g v).2) := by
  simp only [insR, chain_add_high h z g v hh]
  congr 1
  abel

/-- Adding an interval at the insertion row that is not above the picked one. -/
theorem insR_add_of_pick {a : Multisegment} {g v : ℤ} {I J : Interval}
    (hp : pick a g v = some I) (hJe : J.ending = g) (hJb : J.beginning ≤ I.beginning) :
    insR (a + {J}) g v = ((insR a g v).1 + {J}, (insR a g v).2) := by
  have hI := pick_mem hp
  have hs := pick_spec hp
  have hp' : pick (a + {J}) g v = some I := by
    rw [pick_eq_some_iff]
    refine ⟨Multiset.mem_add.mpr (Or.inl hI), hs.1, hs.2, fun K hK hKe hKb => ?_⟩
    rcases Multiset.mem_add.mp hK with hK | hK
    · exact pick_maximal hp hK hKe hKb
    · rw [Multiset.mem_singleton] at hK
      subst hK
      exact hJb
  rw [insR_of_pick_some hp', insR_of_pick_some hp, Multiset.erase_add_left_pos _ hI,
    add_comm (a.erase I), insR_add_high _ _ (by
      intro K hK
      rw [Multiset.mem_singleton] at hK
      subst hK
      omega)]
  congr 1
  exact add_right_comm _ _ _

/-- Insertion at a row whose entries are all at least the letter. -/
theorem rd1_none {M : Multiset ℤ} {z' : Multisegment} {g v : ℤ} (hM : ∀ x ∈ M, v ≤ x)
    (hz : ∀ J ∈ z', J.ending < g) :
    insR (place M g + z') g v = (place (M + {v}) g + z', 0) := by
  have hp : pick (place M g + z') g v = none := by
    rw [pick_none_iff]
    intro I hI
    rcases Multiset.mem_add.mp hI with hI | hI
    · exact Or.inr (hM _ (mem_place.mp hI).1)
    · exact Or.inl (by have := hz I hI; omega)
  rw [insR_of_pick_none hp, place_add, place_singleton]
  congr 1
  abel

/-- Insertion at a row bumping its largest entry `m` below the letter. -/
theorem rd1_some {M : Multiset ℤ} {z' : Multisegment} {g v m : ℤ} (hm : m ∈ M) (hmv : m < v)
    (hmax : ∀ x ∈ M, x < v → x ≤ m) (hv : v ≤ g + 1) (hz : ∀ J ∈ z', J.ending < g) :
    insR (place M g + z') g v =
      ((insR z' (g - 1) m).1 + place (M.erase m + {v}) g, (insR z' (g - 1) m).2 + 1) := by
  have hmg : m ≤ g := by omega
  have hI : (⟨m, g, hmg⟩ : Interval) ∈ place M g := mem_place.mpr ⟨hm, rfl⟩
  have hp : pick (place M g + z') g v = some ⟨m, g, hmg⟩ := by
    rw [pick_eq_some_iff]
    refine ⟨Multiset.mem_add.mpr (Or.inl hI), rfl, hmv, fun K hK hKe hKb => ?_⟩
    rcases Multiset.mem_add.mp hK with hK | hK
    · exact hmax _ (mem_place.mp hK).1 hKb
    · have := hz K hK
      omega
  rw [insR_of_pick_some hp]
  dsimp only
  rw [Multiset.erase_add_left_pos _ hI, place_erase hm hmg,
    insR_add_high _ _ (fun J hJ => by have := (mem_place.mp hJ).2; omega), place_add,
    place_singleton]
  congr 1
  exact add_assoc _ _ _

theorem insR_endings (a : Multisegment) : ∀ g v k : ℤ, (∀ J ∈ a, J.ending ≤ k) → g ≤ k →
    ∀ J ∈ (insR a g v).1, J.ending ≤ k := by
  induction a using (measure (fun a : Multisegment => a.card)).wf.induction with
  | h a ih =>
    intro g v k ha hg
    have hseg : ∀ J ∈ seg v g, J.ending ≤ k := fun J hJ => by rw [(mem_seg.mp hJ).2]; exact hg
    cases hp : pick a g v with
    | none =>
      rw [insR_of_pick_none hp]
      intro J hJ
      rcases Multiset.mem_add.mp hJ with hJ | hJ
      · exact ha J hJ
      · exact hseg J hJ
    | some I =>
      rw [insR_of_pick_some hp]
      intro J hJ
      rcases Multiset.mem_add.mp hJ with hJ | hJ
      · exact ih (a.erase I) (Multiset.card_erase_lt_of_mem (pick_mem hp)) (g - 1) I.beginning k
          (fun K hK => ha K (Multiset.mem_of_mem_erase hK)) (by omega) J hJ
      · exact hseg J hJ

theorem insR_weight (a : Multisegment) : ∀ g v : ℤ,
    weight (insR a g v).1 + (insR a g v).2 = weight a + (g + 1 - v).toNat := by
  induction a using (measure (fun a : Multisegment => a.card)).wf.induction with
  | h a ih =>
    intro g v
    cases hp : pick a g v with
    | none =>
      rw [insR_of_pick_none hp]
      simp only [weight_add, weight_seg]
      omega
    | some I =>
      rw [insR_of_pick_some hp]
      have h1 := ih (a.erase I) (Multiset.card_erase_lt_of_mem (pick_mem hp)) (g - 1) I.beginning
      have h2 := weight_erase (pick_mem hp)
      have h3 := (pick_spec hp).1
      simp only [weight_add, weight_seg, Interval.length] at h1 h2 ⊢
      rw [h3] at h2
      omega

/-! ## Word insertion -/

/-- Insert the letters of a word successively at the same row, recording bump counts. -/
def insW : Multisegment → ℤ → List ℤ → Multisegment × List ℕ
  | a, _, [] => (a, [])
  | a, g, c :: w => ((insW (insR a g c).1 g w).1, (insR a g c).2 :: (insW (insR a g c).1 g w).2)

@[simp] theorem insW_nil (a : Multisegment) (g : ℤ) : insW a g [] = (a, []) := rfl

theorem insW_cons (a : Multisegment) (g c : ℤ) (w : List ℤ) :
    insW a g (c :: w) =
      ((insW (insR a g c).1 g w).1, (insR a g c).2 :: (insW (insR a g c).1 g w).2) := rfl

theorem insW_length (w : List ℤ) : ∀ (a : Multisegment) (g : ℤ),
    (insW a g w).2.length = w.length := by
  induction w with
  | nil => simp
  | cons c w ih => intro a g; simp [insW_cons, ih]

theorem insW_append (w₁ w₂ : List ℤ) : ∀ (a : Multisegment) (g : ℤ),
    insW a g (w₁ ++ w₂) =
      ((insW (insW a g w₁).1 g w₂).1, (insW a g w₁).2 ++ (insW (insW a g w₁).1 g w₂).2) := by
  induction w₁ with
  | nil => simp
  | cons c w ih => intro a g; simp [insW_cons, ih]

theorem insW_endings (w : List ℤ) : ∀ (a : Multisegment) (g k : ℤ), (∀ J ∈ a, J.ending ≤ k) →
    g ≤ k → ∀ J ∈ (insW a g w).1, J.ending ≤ k := by
  induction w with
  | nil => intro a g k ha _; simpa using ha
  | cons c w ih =>
    intro a g k ha hg
    rw [insW_cons]
    exact ih _ g k (insR_endings a g c k ha hg) hg

theorem insW_weight (w : List ℤ) : ∀ (a : Multisegment) (g : ℤ),
    weight (insW a g w).1 + (insW a g w).2.sum =
      weight a + (w.map fun c => (g + 1 - c).toNat).sum := by
  induction w with
  | nil => simp
  | cons c w ih =>
    intro a g
    have h1 := ih (insR a g c).1 g
    have h2 := insR_weight a g c
    simp only [insW_cons, List.sum_cons, List.map_cons]
    omega

/-! ## Rows -/

/-- Beginnings of the intervals ending at `g`. -/
def rowM (z : Multisegment) (g : ℤ) : Multiset ℤ :=
  (z.filter fun J => J.ending = g).map Interval.beginning

/-- Row `g` as a weakly decreasing list. -/
def rowL (z : Multisegment) (g : ℤ) : List ℤ := (rowM z g).sort (fun x y => y ≤ x)

/-- The intervals ending strictly below `g`. -/
def low (z : Multisegment) (g : ℤ) : Multisegment := z.filter fun J => J.ending < g

theorem rowL_coe (z : Multisegment) (g : ℤ) : ((rowL z g : List ℤ) : Multiset ℤ) = rowM z g :=
  Multiset.sort_eq _ _

theorem rowL_desc (z : Multisegment) (g : ℤ) : Desc (rowL z g) := Multiset.pairwise_sort _ _

theorem mem_rowM {z : Multisegment} {g x : ℤ} :
    x ∈ rowM z g ↔ ∃ J ∈ z, J.ending = g ∧ J.beginning = x := by
  simp only [rowM, Multiset.mem_map, Multiset.mem_filter, and_assoc]

theorem mem_rowL {z : Multisegment} {g x : ℤ} :
    x ∈ rowL z g ↔ ∃ J ∈ z, J.ending = g ∧ J.beginning = x := by
  rw [← mem_rowM, ← rowL_coe, Multiset.mem_coe]

theorem rowL_le {z : Multisegment} {g x : ℤ} (h : x ∈ rowL z g) : x ≤ g := by
  obtain ⟨J, -, hJe, hJb⟩ := mem_rowL.mp h
  have := J.nonempty
  omega

theorem low_endings (z : Multisegment) (g : ℤ) : ∀ J ∈ low z g, J.ending < g :=
  fun _ hJ => (Multiset.mem_filter.mp hJ).2

theorem place_rowM (z : Multisegment) (g : ℤ) :
    place (rowM z g) g = z.filter fun J => J.ending = g := by
  induction z using Multiset.induction_on with
  | empty => simp [rowM]
  | cons J z ih =>
    by_cases hJ : J.ending = g
    · rw [rowM, Multiset.filter_cons_of_pos (p := fun J : Interval => J.ending = g) _ hJ,
        Multiset.map_cons, place_cons, ← rowM, ih, ← hJ, seg_self, Multiset.singleton_add]
    · rw [rowM, Multiset.filter_cons_of_neg (p := fun J : Interval => J.ending = g) _ hJ,
        ← rowM, ih]

theorem decomp (z : Multisegment) (g : ℤ) (h : ∀ J ∈ z, J.ending ≤ g) :
    z = place ↑(rowL z g) g + low z g := by
  rw [rowL_coe, place_rowM, low]
  have : z.filter (fun J => J.ending < g) = z.filter (fun J => ¬ J.ending = g) :=
    Multiset.filter_congr (fun J hJ => by
      have := h J hJ
      constructor <;> intro <;> omega)
  rw [this, Multiset.filter_add_not]

/-! ## The bridge between `dual` and insertion -/

theorem round_of_pick {a : Multisegment} {e : ℤ} {I : Interval} (ha : ∀ J ∈ a, J.ending ≤ e)
    (hp : pick a e (e + 1) = some I) :
    round a = some ⟨I, (chain (a.erase I) (e - 1) I.beginning).1,
      (chain (a.erase I) (e - 1) I.beginning).2⟩ := by
  have hI := pick_mem hp
  have hIe := (pick_spec hp).1
  have hsort := Multiset.sort_eq a (fun I J : Interval => J ≤ I)
  have hpw := Multiset.pairwise_sort a (fun I J : Interval => J ≤ I)
  unfold round
  cases hs : a.sort (fun I J : Interval => J ≤ I) with
  | nil =>
    rw [hs] at hsort
    rw [← hsort] at hI
    simp at hI
  | cons K l =>
    rw [hs] at hsort hpw
    have hKa : K ∈ a := by
      rw [← hsort]
      exact Multiset.mem_coe.mpr List.mem_cons_self
    have hKI : K = I := by
      apply le_antisymm
      · rw [interval_le_iff]
        have hKe := ha K hKa
        rcases lt_or_eq_of_le hKe with h | h
        · left
          omega
        · right
          exact ⟨by omega, pick_maximal hp hKa h (by have := K.nonempty; omega)⟩
      · have hIl : I ∈ K :: l := by
          rw [← hsort] at hI
          exact Multiset.mem_coe.mp hI
        rcases List.mem_cons.mp hIl with h | h
        · exact le_of_eq h
        · exact (List.pairwise_cons.mp hpw).1 I h
    have hl : (l : Multiset Interval) = a.erase I := by
      rw [← hsort, ← Multiset.cons_coe, hKI, Multiset.erase_cons_head]
    simp only [hKI, hl, hIe]

/-- One MW round of a multisegment with endings `≤ e` is the insertion of `e+1` at row `e`. -/
theorem bridge {a : Multisegment} {e : ℤ} (ha : ∀ J ∈ a, J.ending ≤ e) :
    dual a = emit e (insR a e (e + 1)).2 + dual (insR a e (e + 1)).1 := by
  cases hp : pick a e (e + 1) with
  | none =>
    rw [insR_of_pick_none hp, emit, seg_of_lt (by omega), seg_of_lt (by omega)]
    simp
  | some I =>
    have hIe := (pick_spec hp).1
    rw [dual_of_round (round_of_pick ha hp), insR_of_pick_some hp,
      seg_of_lt (show e < e + 1 by omega), add_zero, emit]
    rw [seg_of_le (show e + 1 - (((insR (a.erase I) (e - 1) I.beginning).2 + 1 : ℕ) : ℤ) ≤ e by
      omega), Multiset.singleton_add]
    congr 1
    · apply Interval.ext
      · simp only [Round.emitted, insR, hIe]
        push_cast
        ring
      · simp only [Round.emitted, hIe]
    · congr 1
      simp only [Round.residual, Round.selected, Round.selectedList, insR, ← Multiset.cons_coe,
        shorten_cons, dropLast_eq, hIe]
      abel

theorem dual_endings (a : Multisegment) : ∀ e : ℤ, (∀ J ∈ a, J.ending ≤ e) →
    ∀ J ∈ dual a, J.ending ≤ e := by
  induction a using (measure weight).wf.induction with
  | h a ih =>
    intro e ha
    cases hr : round a with
    | none =>
      rw [(round_none_iff a).mp hr, dual_zero]
      simp
    | some r =>
      rw [dual_of_round hr]
      have hpart := round_partition hr
      intro J hJ
      rcases Multiset.mem_cons.mp hJ with hJ | hJ
      · subst hJ
        simp only [Round.emitted]
        apply ha
        rw [← hpart]
        simp [Round.selected, Round.selectedList]
      · refine ih r.residual (round_weight_lt hr) e ?_ J hJ
        intro K hK
        rcases Multiset.mem_add.mp hK with hK | hK
        · exact ha K (by rw [← hpart]; exact Multiset.mem_add.mpr (Or.inr hK))
        · obtain ⟨I, hI, -, hKe⟩ := mem_shorten hK
          have := ha I (by rw [← hpart]; exact Multiset.mem_add.mpr (Or.inl hI))
          omega

/-- Processing a whole top row: each entry is inserted one row below, and the
bump counts determine the emitted intervals. -/
theorem rowProc (C : List ℤ) : ∀ (f : ℤ) (z : Multisegment), Desc C → (∀ c ∈ C, c ≤ f) →
    (∀ J ∈ z, J.ending ≤ f - 1) →
    dual (place ↑C f + z) =
      place ↑((insW z (f - 1) C).2.map (fun r : ℕ => f - (r : ℤ))) f +
        dual (insW z (f - 1) C).1 := by
  induction C with
  | nil => intro f z _ _ _; simp
  | cons c C ih =>
    intro f z hC hCf hz
    have hy : ∀ J ∈ place ↑(c :: C) f + z, J.ending ≤ f := by
      intro J hJ
      rcases Multiset.mem_add.mp hJ with hJ | hJ
      · exact (mem_place.mp hJ).2.le
      · have := hz J hJ
        omega
    rw [bridge hy]
    have hcmax : ∀ x ∈ (↑(c :: C) : Multiset ℤ), x < f + 1 → x ≤ c := by
      intro x hx _
      rcases List.mem_cons.mp (Multiset.mem_coe.mp hx) with rfl | hx
      · exact le_rfl
      · exact (List.pairwise_cons.mp hC).1 x hx
    have hcf : c ≤ f := hCf c List.mem_cons_self
    rw [rd1_some (m := c) (Multiset.mem_coe.mpr List.mem_cons_self) (by omega) hcmax le_rfl
      (fun J hJ => by have := hz J hJ; omega)]
    have hz1 : ∀ J ∈ (insR z (f - 1) c).1, J.ending ≤ f - 1 :=
      insR_endings z (f - 1) c (f - 1) hz le_rfl
    dsimp only
    rw [← Multiset.cons_coe, Multiset.erase_cons_head, place_add, place_singleton,
      seg_of_lt (by omega : f < f + 1), add_zero, add_comm (insR z (f - 1) c).1,
      ih f _ (List.pairwise_cons.mp hC).2 (fun x hx => hCf x (List.mem_cons_of_mem _ hx)) hz1]
    simp only [insW_cons, List.map_cons, ← Multiset.cons_coe, place_cons, emit]
    have : f + 1 - (((insR z (f - 1) c).2 + 1 : ℕ) : ℤ) = f - ((insR z (f - 1) c).2 : ℤ) := by
      push_cast
      ring
    rw [this, add_assoc]

end Langlands.MoeglinWaldspurger.Involution
