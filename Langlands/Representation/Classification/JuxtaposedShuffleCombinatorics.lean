import Langlands.Representation.Classification.TwoSegmentSocleShuffleJacquetStatement

/-!
# Shuffle combinatorics for two juxtaposed segments

Elementary facts about the shuffle exponents `shuffleExponent S a₀ a₁` of
`TwoSegmentSocleShuffleJacquetStatement`: adjacent transpositions of shuffle sets,
and, for the juxtaposed runs `p, …, p+q-1` and `0, …, p-1`, injectivity and
reachability of every shuffle except the identity one by unlinked moves.
-/

namespace Langlands.Classification.JuxtaposedShuffle

open Finset

/-- An adjacent transposition preserves the order of every pair other than
`{i, j}`. -/
theorem swap_lt_swap_iff {m : ℕ} {i j x k : Fin m} (hij : j.val = i.val + 1)
    (h₁ : ¬ (x = i ∧ k = j)) (h₂ : ¬ (x = j ∧ k = i)) :
    Equiv.swap i j x < Equiv.swap i j k ↔ x < k := by
  simp only [Fin.ext_iff] at h₁ h₂
  simp only [Equiv.swap_apply_def]
  split_ifs <;> simp only [Fin.ext_iff, Fin.lt_def] at * <;> omega

/-- The shuffle set obtained from `S` by exchanging the positions `i` and `j`. -/
def swapShuffle {m : ℕ} (S : Finset (Fin m)) (i j : Fin m) : Finset (Fin m) :=
  S.map (Equiv.swap i j).toEmbedding

theorem mem_swapShuffle {m : ℕ} {S : Finset (Fin m)} {i j x : Fin m} :
    x ∈ swapShuffle S i j ↔ Equiv.swap i j x ∈ S := by
  simp [swapShuffle, Finset.mem_map_equiv, Equiv.symm_swap]

theorem card_swapShuffle {m : ℕ} (S : Finset (Fin m)) (i j : Fin m) :
    (swapShuffle S i j).card = S.card := by
  simp [swapShuffle]

theorem swapShuffle_swapShuffle {m : ℕ} (S : Finset (Fin m)) (i j : Fin m) :
    swapShuffle (swapShuffle S i j) i j = S := by
  ext x; simp [mem_swapShuffle]

theorem compl_swapShuffle {m : ℕ} (S : Finset (Fin m)) (i j : Fin m) :
    (swapShuffle S i j)ᶜ = swapShuffle Sᶜ i j := by
  ext x; simp [mem_swapShuffle]

theorem card_filter_swapShuffle {m : ℕ} {S : Finset (Fin m)} {i j k : Fin m}
    (hij : j.val = i.val + 1) (hS : ¬ (i ∈ S ∧ j ∈ S)) (hk : k ∈ S) :
    ((swapShuffle S i j).filter (· < Equiv.swap i j k)).card = (S.filter (· < k)).card := by
  rw [swapShuffle, Finset.filter_map, Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro x hx
  exact swap_lt_swap_iff hij (fun h => hS ⟨h.1 ▸ hx, h.2 ▸ hk⟩)
    (fun h => hS ⟨h.2 ▸ hk, h.1 ▸ hx⟩)

/-- Exchanging an adjacent pair `i, j = i + 1` of positions, exactly one of which
lies in `S`, permutes the shuffle exponents by the same transposition. -/
theorem shuffleExponent_swapShuffle_apply {m : ℕ} (S : Finset (Fin m)) (a₀ a₁ : ℝ)
    {i j : Fin m} (hij : j.val = i.val + 1) (hS : i ∈ S ↔ j ∉ S) (k : Fin m) :
    shuffleExponent (swapShuffle S i j) a₀ a₁ (Equiv.swap i j k) =
      shuffleExponent S a₀ a₁ k := by
  unfold shuffleExponent
  have hmem : Equiv.swap i j k ∈ swapShuffle S i j ↔ k ∈ S := by simp [mem_swapShuffle]
  by_cases hk : k ∈ S
  · rw [ite_eq_left (hmem.2 hk), ite_eq_left hk, card_filter_swapShuffle hij (by tauto) hk]
  · rw [ite_eq_right (mt hmem.1 hk), ite_eq_right hk, compl_swapShuffle,
      card_filter_swapShuffle hij (by simp only [mem_compl]; tauto) (mem_compl.2 hk)]

theorem shuffleExponent_swapShuffle {m : ℕ} (S : Finset (Fin m)) (a₀ a₁ : ℝ)
    {i j : Fin m} (hij : j.val = i.val + 1) (hS : i ∈ S ↔ j ∉ S) :
    shuffleExponent (swapShuffle S i j) a₀ a₁ =
      fun k => shuffleExponent S a₀ a₁ (Equiv.swap i j k) := by
  funext k
  simpa using shuffleExponent_swapShuffle_apply S a₀ a₁ hij hS (Equiv.swap i j k)

/-! ### The juxtaposed runs `p, …, p+q-1` and `0, …, p-1` -/

/-- The initial shuffle `{0, …, q-1}`: the run of `Δ` comes first. -/
def initShuffle (q p : ℕ) : Finset (Fin (q + p)) := univ.filter (fun k => k.val < q)

/-- The identity shuffle `{p, …, p+q-1}`: the exponents are `0, 1, …, p+q-1`. -/
def idShuffle (q p : ℕ) : Finset (Fin (q + p)) := univ.filter (fun k => p ≤ k.val)

theorem le_shuffleExponent {m : ℕ} {S : Finset (Fin m)} (a₀ a₁ : ℝ) {k : Fin m}
    (hk : k ∈ S) : a₀ ≤ shuffleExponent S a₀ a₁ k := by
  unfold shuffleExponent
  rw [ite_eq_left hk]
  exact le_add_of_nonneg_right (Nat.cast_nonneg _)

theorem card_compl_of_card {q p : ℕ} {S : Finset (Fin (q + p))} (hS : S.card = q) :
    Sᶜ.card = p := by
  rw [Finset.card_compl, Fintype.card_fin, hS]; omega

theorem card_filter_compl_lt {q p : ℕ} {S : Finset (Fin (q + p))} (hS : S.card = q)
    {k : Fin (q + p)} (hk : k ∉ S) : (Sᶜ.filter (· < k)).card < p := by
  exact lt_of_lt_of_eq
    (Finset.card_lt_card (Finset.filter_ssubset.2 ⟨k, mem_compl.2 hk, lt_irrefl k⟩))
    (card_compl_of_card hS)

theorem shuffleExponent_lt {q p : ℕ} {S : Finset (Fin (q + p))} (hS : S.card = q)
    {k : Fin (q + p)} (hk : k ∉ S) : shuffleExponent S (p : ℝ) 0 k < p := by
  unfold shuffleExponent
  rw [ite_eq_right hk, zero_add]
  exact_mod_cast card_filter_compl_lt hS hk

theorem mem_iff_le_shuffleExponent {q p : ℕ} {S : Finset (Fin (q + p))} (hS : S.card = q)
    (k : Fin (q + p)) : k ∈ S ↔ (p : ℝ) ≤ shuffleExponent S (p : ℝ) 0 k :=
  ⟨le_shuffleExponent _ _, fun h => by
    by_contra hk
    exact absurd (shuffleExponent_lt hS hk) (not_lt.2 h)⟩

/-- For the juxtaposed runs, a shuffle set of size `q` is determined by its exponents. -/
theorem eq_of_shuffleExponent_eq {q p : ℕ} {S S' : Finset (Fin (q + p))}
    (hS : S.card = q) (hS' : S'.card = q)
    (h : ∀ k, shuffleExponent S (p : ℝ) 0 k = shuffleExponent S' (p : ℝ) 0 k) : S = S' := by
  ext k
  rw [mem_iff_le_shuffleExponent hS, mem_iff_le_shuffleExponent hS', h]

/-- A right move `i ∈ S`, `i + 1 ∉ S` exchanges exponents that differ by at least one;
they differ by exactly one only when the move produces the identity shuffle. -/
theorem shuffleExponent_lt_of_move {q p : ℕ} {S : Finset (Fin (q + p))} (hS : S.card = q)
    {i j : Fin (q + p)} (hi : i ∈ S) (hj : j ∉ S) :
    shuffleExponent S (p : ℝ) 0 j < shuffleExponent S (p : ℝ) 0 i :=
  lt_of_lt_of_le (shuffleExponent_lt hS hj) (le_shuffleExponent _ _ hi)

theorem swapShuffle_eq_idShuffle_of_gap {q p : ℕ} {S : Finset (Fin (q + p))}
    (hS : S.card = q) {i j : Fin (q + p)} (hij : j.val = i.val + 1) (hi : i ∈ S)
    (hj : j ∉ S)
    (hgap : shuffleExponent S (p : ℝ) 0 i = shuffleExponent S (p : ℝ) 0 j + 1) :
    swapShuffle S i j = idShuffle q p := by
  have hd := card_filter_compl_lt hS hj
  unfold shuffleExponent at hgap
  rw [ite_eq_left hi, ite_eq_right hj, zero_add] at hgap
  have hgap' : p + (S.filter (· < i)).card = (Sᶜ.filter (· < j)).card + 1 := by
    exact_mod_cast hgap
  have hc : (S.filter (· < i)).card = 0 := by omega
  have hbelow : ∀ x ∈ S, ¬ x < i := by
    intro x hx hlt
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hc
    exact hc hx hlt
  have hfilter : Sᶜ.filter (· < j) = univ.filter (fun x : Fin (q + p) => x.val < i.val) := by
    ext x
    simp only [mem_filter, mem_compl, mem_univ, true_and, Fin.lt_def]
    constructor
    · rintro ⟨hx, hxj⟩
      have : x ≠ i := fun h => hx (h ▸ hi)
      rw [Ne, Fin.ext_iff] at this
      omega
    · intro hx
      exact ⟨fun hxS => hbelow x hxS (Fin.lt_def.2 hx), by omega⟩
  have hival : i.val = (Sᶜ.filter (· < j)).card := by
    rw [hfilter, Fin.card_filter_val_lt]; omega
  have habove : ∀ x : Fin (q + p), j < x → x ∈ S := by
    intro x hjx
    by_contra hx
    have hsub : insert x (insert j (Sᶜ.filter (· < j))) ⊆ Sᶜ := by
      intro y hy
      simp only [mem_insert, mem_filter] at hy
      rcases hy with rfl | rfl | hy
      · exact mem_compl.2 hx
      · exact mem_compl.2 hj
      · exact hy.1
    have hcard := Finset.card_le_card hsub
    rw [card_compl_of_card hS, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
      at hcard
    · omega
    · simp
    · simp only [mem_insert, mem_filter, not_or]
      exact ⟨fun h => (lt_irrefl j) (h ▸ hjx), fun h => lt_asymm hjx h.2⟩
  ext y
  rw [mem_swapShuffle]
  simp only [idShuffle, mem_filter, mem_univ, true_and]
  by_cases hyi : y = i
  · subst hyi; rw [Equiv.swap_apply_left]; simp only [hj, false_iff]; omega
  by_cases hyj : y = j
  · subst hyj; rw [Equiv.swap_apply_right]; simp only [hi, true_iff]; omega
  rw [Equiv.swap_apply_of_ne_of_ne hyi hyj]
  simp only [Fin.ext_iff] at hyi hyj
  constructor
  · intro hy
    have := hbelow y hy
    rw [Fin.lt_def] at this
    omega
  · intro hy
    exact habove y (Fin.lt_def.2 (by omega))

theorem exists_left_move {m : ℕ} {S : Finset (Fin m)} (hS : S ≠ univ.filter (fun k => k.val < S.card)) :
    ∃ i j : Fin m, j.val = i.val + 1 ∧ i ∉ S ∧ j ∈ S := by
  by_contra h
  push Not at h
  have hdown : ∀ d : ℕ, ∀ x y : Fin m, x.val = y.val + d → x ∈ S → y ∈ S := by
    intro d
    induction d with
    | zero => intro x y hxy hx; rwa [show y = x from Fin.ext (by omega)]
    | succ d ih =>
      intro x y hxy hx
      have hk : y.val + 1 < m := by omega
      exact h y ⟨y.val + 1, hk⟩ rfl |>.mt (not_not.2 (ih x ⟨y.val + 1, hk⟩ (by simp; omega) hx))
        |> not_not.1
  apply hS
  ext k
  simp only [mem_filter, mem_univ, true_and]
  have := Fin.lt_card_filter_univ_iff_apply_of_imp (j := k) (· ∈ S)
    (fun x y hyx hx => hdown (x.val - y.val) x y (by rw [Fin.le_def] at hyx; omega) hx)
  rw [Finset.filter_univ_mem] at this
  exact this.symm

theorem card_initShuffle (q p : ℕ) : (initShuffle q p).card = q := by
  rw [initShuffle, Fin.card_filter_val_lt]; omega

theorem card_idShuffle (q p : ℕ) : (idShuffle q p).card = q := by
  have h : idShuffle q p = (univ.filter (fun k : Fin (q + p) => k.val < p))ᶜ := by
    ext k; simp [idShuffle]
  rw [h, card_compl, Fintype.card_fin, Fin.card_filter_val_lt]; omega

/-- Every shuffle set of size `q` other than the identity one is reached from the
initial shuffle `{0, …, q-1}` by right moves `i ∈ S`, `i + 1 ∉ S` whose exchanged
exponents do not differ by exactly one. -/
theorem shuffle_induction {q p : ℕ} (P : Finset (Fin (q + p)) → Prop)
    (h₀ : P (initShuffle q p))
    (hmove : ∀ (S : Finset (Fin (q + p))) (i j : Fin (q + p)), S.card = q →
      j.val = i.val + 1 → i ∈ S → j ∉ S →
      shuffleExponent S (p : ℝ) 0 i ≠ shuffleExponent S (p : ℝ) 0 j + 1 →
      P S → P (swapShuffle S i j))
    (S : Finset (Fin (q + p))) (hS : S.card = q) (hid : S ≠ idShuffle q p) : P S := by
  induction hn : ∑ k ∈ S, (k : ℕ) using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    by_cases h0 : S = initShuffle q p
    · exact h0 ▸ h₀
    obtain ⟨i, j, hij, hi, hj⟩ := exists_left_move (S := S) (by rw [hS]; exact h0)
    have hS'' : (swapShuffle S i j).card = q := by rw [card_swapShuffle, hS]
    have hi'' : i ∈ swapShuffle S i j := by
      rw [mem_swapShuffle, Equiv.swap_apply_left]; exact hj
    have hj'' : j ∉ swapShuffle S i j := by
      rw [mem_swapShuffle, Equiv.swap_apply_right]; exact hi
    have hback : swapShuffle (swapShuffle S i j) i j = S := swapShuffle_swapShuffle S i j
    have hid'' : swapShuffle S i j ≠ idShuffle q p := by
      intro h
      rw [h] at hi'' hj''
      simp only [idShuffle, mem_filter, mem_univ, true_and] at hi'' hj''
      omega
    have hsum : ∑ k ∈ swapShuffle S i j, (k : ℕ) < n := by
      rw [← hn, swapShuffle, Finset.sum_map, ← Finset.add_sum_erase S _ hj,
        ← Finset.add_sum_erase S (fun k : Fin (q + p) => (k : ℕ)) hj]
      have hrest : ∑ x ∈ S.erase j, ((Equiv.swap i j).toEmbedding x : ℕ) =
          ∑ x ∈ S.erase j, (x : ℕ) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Equiv.coe_toEmbedding, Equiv.swap_apply_of_ne_of_ne
          (fun h : x = i => hi (h ▸ Finset.mem_of_mem_erase hx)) (Finset.ne_of_mem_erase hx)]
      rw [hrest, Equiv.coe_toEmbedding, Equiv.swap_apply_right]
      omega
    have hP'' := ih _ hsum (swapShuffle S i j) hS'' hid'' rfl
    rw [← hback]
    refine hmove _ i j hS'' hij hi'' hj'' (fun hgap => hid ?_) hP''
    rw [← hback]
    exact swapShuffle_eq_idShuffle_of_gap hS'' hij hi'' hj'' hgap

theorem initShuffle_ne_idShuffle {q p : ℕ} (hq : 0 < q) (hp : 0 < p) :
    initShuffle q p ≠ idShuffle q p := by
  intro h
  have h0 : (⟨0, by omega⟩ : Fin (q + p)) ∈ initShuffle q p := by
    simp [initShuffle, hq]
  rw [h] at h0
  simp [idShuffle] at h0
  omega

theorem shuffleExponent_initShuffle_zero {q p : ℕ} (hq : 0 < q) :
    shuffleExponent (initShuffle q p) (p : ℝ) 0 ⟨0, by omega⟩ = p := by
  unfold shuffleExponent
  rw [ite_eq_left (by simp [initShuffle, hq])]
  simp [Fin.lt_def]

end Langlands.Classification.JuxtaposedShuffle
