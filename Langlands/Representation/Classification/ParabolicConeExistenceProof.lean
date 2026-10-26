import Langlands.Representation.Classification.ParabolicConeAuxiliaryStatement

/-!
# Existence of the numerical block cone

Proof of `Langlands.GLBlockConeExistenceStatement` by pooling adjacent violators.
A *pooling* of weighted values is a monotone surjective labelling of the blocks
whose inclusive residual prefix sums against the fibre means are nonpositive.
The identity labelling is a pooling; merging two adjacent fibres whose means are
not strictly decreasing gives a pooling with one label fewer. Induction on the
number of labels gives a pooling with strictly decreasing means, and its fibre
sizes form the coarse block shape.
-/

noncomputable section

namespace Langlands

open Finset GeneralLinear

namespace ParabolicConeExistence

/-- The value of `Fin.predAbove`: labels above `p.castSucc` move down by one. -/
theorem val_predAbove {m : ℕ} (p : Fin m) (a : Fin (m + 1)) :
    (p.predAbove a).val = if p.val < a.val then a.val - 1 else a.val := by
  have hiff : Fin.castSucc p < a ↔ p.val < a.val := by simp [Fin.lt_def]
  unfold Fin.predAbove
  by_cases h : p.val < a.val
  · simp [hiff.mpr h, h]
  · have h' : ¬Fin.castSucc p < a := fun h' => h (hiff.mp h')
    simp [h', h]

/-- Exactly the two labels `p.castSucc` and `p.succ` collapse onto `p`. -/
theorem predAbove_eq_self_iff {m : ℕ} (p : Fin m) (a : Fin (m + 1)) :
    p.predAbove a = p ↔ a = p.castSucc ∨ a = p.succ := by
  rw [Fin.ext_iff, val_predAbove, Fin.ext_iff, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> omega

/-- Away from the merged label, `Fin.predAbove` is injective. -/
theorem predAbove_eq_predAbove_iff {m : ℕ} (p : Fin m) {a b : Fin (m + 1)}
    (ha : p.predAbove a ≠ p) : p.predAbove b = p.predAbove a ↔ b = a := by
  constructor
  · intro h
    rw [Ne, Fin.ext_iff, val_predAbove] at ha
    rw [Fin.ext_iff, val_predAbove, val_predAbove] at h
    rw [Fin.ext_iff]
    split_ifs at ha h <;> omega
  · rintro rfl
    rfl

variable {L : ℕ}

/-- The blocks carrying the label `j`. -/
abbrev fibre {m : ℕ} (q : Fin L → Fin m) (j : Fin m) : Finset (Fin L) :=
  univ.filter (fun i => q i = j)

/-- The total real weight of the fibre over `j`. -/
def fibreWeight (w : Fin L → ℕ) {m : ℕ} (q : Fin L → Fin m) (j : Fin m) : ℝ :=
  ∑ i ∈ fibre q j, (w i : ℝ)

/-- The weighted mean of `r` on the fibre over `j`. -/
def fibreMean (w : Fin L → ℕ) (r : Fin L → ℝ) {m : ℕ} (q : Fin L → Fin m)
    (j : Fin m) : ℝ :=
  (∑ i ∈ fibre q j, r i) / fibreWeight w q j

/-- A pooling of the weighted values `r`: consecutive nonempty fibres whose inclusive
residual prefix sums against the fibre means are nonpositive. -/
structure IsPooling (w : Fin L → ℕ) (r : Fin L → ℝ) {m : ℕ} (q : Fin L → Fin m) :
    Prop where
  monotone : Monotone q
  surjective : Function.Surjective q
  residual_nonpos : ∀ i, (∑ k ∈ univ.filter (fun k => q k = q i ∧ k ≤ i),
    (r k - (w k : ℝ) * fibreMean w r q (q i))) ≤ 0

variable {w : Fin L → ℕ} {r : Fin L → ℝ}

theorem fibreWeight_pos (hw : ∀ i, 0 < w i) {m : ℕ} {q : Fin L → Fin m}
    (hq : Function.Surjective q) (j : Fin m) : 0 < fibreWeight w q j := by
  obtain ⟨i, hi⟩ := hq j
  exact Finset.sum_pos (fun k _ => by exact_mod_cast hw k) ⟨i, by simp [hi]⟩

/-- The sum of `r` over a fibre is its weight times its mean. -/
theorem sum_fibre_eq (hw : ∀ i, 0 < w i) {m : ℕ} {q : Fin L → Fin m}
    (hq : Function.Surjective q) (j : Fin m) :
    ∑ i ∈ fibre q j, r i = fibreWeight w q j * fibreMean w r q j := by
  unfold fibreMean
  rw [mul_div_cancel₀ _ (fibreWeight_pos hw hq j).ne']

/-- The singleton labelling is a pooling, with zero residuals. -/
theorem isPooling_id (hw : ∀ i, 0 < w i) : IsPooling w r (fun i : Fin L => i) where
  monotone := monotone_id
  surjective := Function.surjective_id
  residual_nonpos i := by
    have hset : univ.filter (fun k : Fin L => k = i ∧ k ≤ i) = {i} := by
      ext k
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · exact fun h => h.1
      · rintro rfl
        exact ⟨rfl, le_rfl⟩
    have hfib : fibre (fun k : Fin L => k) i = {i} := by
      ext k
      simp [fibre]
    have hwi : (w i : ℝ) ≠ 0 := by exact_mod_cast (hw i).ne'
    rw [hset, Finset.sum_singleton]
    unfold fibreMean fibreWeight
    rw [hfib, Finset.sum_singleton, Finset.sum_singleton, mul_div_cancel₀ _ hwi, sub_self]

/-- Merging two adjacent fibres whose means are not strictly decreasing preserves the
pooling property. -/
theorem IsPooling.merge (hw : ∀ i, 0 < w i) {m : ℕ} {q : Fin L → Fin (m + 2)}
    (h : IsPooling w r q) (p : Fin (m + 1))
    (hp : fibreMean w r q p.castSucc ≤ fibreMean w r q p.succ) :
    IsPooling w r (fun k => p.predAbove (q k)) := by
  have hcs : p.castSucc < p.succ := Fin.castSucc_lt_succ
  -- The merged fibre is the disjoint union of the two old fibres.
  have hfib : fibre (fun k => p.predAbove (q k)) p = fibre q p.castSucc ∪ fibre q p.succ := by
    ext k
    simp only [fibre, mem_filter, mem_univ, true_and, mem_union]
    exact predAbove_eq_self_iff p (q k)
  have hdisj : Disjoint (fibre q p.castSucc) (fibre q p.succ) := by
    rw [Finset.disjoint_filter]
    intro k _ hk hk'
    rw [hk] at hk'
    exact hcs.ne hk'
  have hsplit : ∀ f : Fin L → ℝ, ∑ k ∈ fibre (fun k => p.predAbove (q k)) p, f k =
      ∑ k ∈ fibre q p.castSucc, f k + ∑ k ∈ fibre q p.succ, f k := by
    intro f
    rw [hfib, Finset.sum_union hdisj]
  have hWc := fibreWeight_pos hw h.surjective p.castSucc
  have hWs := fibreWeight_pos hw h.surjective p.succ
  have hSc := sum_fibre_eq (r := r) hw h.surjective p.castSucc
  have hSs := sum_fibre_eq (r := r) hw h.surjective p.succ
  have hsurj' : Function.Surjective (fun k => p.predAbove (q k)) :=
    (Fin.predAbove_surjective p).comp h.surjective
  have hμ : (fibreWeight w q p.castSucc + fibreWeight w q p.succ) *
      fibreMean w r (fun k => p.predAbove (q k)) p =
      fibreWeight w q p.castSucc * fibreMean w r q p.castSucc +
        fibreWeight w q p.succ * fibreMean w r q p.succ := by
    have hW' : fibreWeight w (fun k => p.predAbove (q k)) p =
        fibreWeight w q p.castSucc + fibreWeight w q p.succ := by
      unfold fibreWeight
      exact hsplit _
    have hS := sum_fibre_eq (r := r) hw hsurj' p
    rw [hsplit, hW', hSc, hSs] at hS
    exact hS.symm
  have hle₁ : fibreMean w r q p.castSucc ≤ fibreMean w r (fun k => p.predAbove (q k)) p := by
    by_contra hlt
    push Not at hlt
    have h₁ := mul_lt_mul_of_pos_left hlt (add_pos hWc hWs)
    have h₂ := mul_le_mul_of_nonneg_left hp hWs.le
    linarith
  have hle₂ : fibreMean w r (fun k => p.predAbove (q k)) p ≤ fibreMean w r q p.succ := by
    by_contra hlt
    push Not at hlt
    have h₁ := mul_lt_mul_of_pos_left hlt (add_pos hWc hWs)
    have h₂ := mul_le_mul_of_nonneg_left hp hWc.le
    linarith
  refine ⟨fun a b hab => Fin.predAbove_right_monotone p (h.monotone hab), hsurj', ?_⟩
  intro i
  by_cases hc : q i = p.castSucc
  · -- The left half of the merged fibre: the mean can only increase.
    have hset : univ.filter (fun k => p.predAbove (q k) = p.predAbove (q i) ∧ k ≤ i) =
        univ.filter (fun k => q k = q i ∧ k ≤ i) := by
      ext k
      simp only [mem_filter, mem_univ, true_and]
      rw [hc, Fin.predAbove_castSucc_self]
      constructor
      · rintro ⟨hk, hki⟩
        refine ⟨?_, hki⟩
        rcases (predAbove_eq_self_iff p (q k)).mp hk with hk' | hk'
        · exact hk'
        · have := h.monotone hki
          rw [hk', hc] at this
          exact absurd this (not_le.mpr hcs)
      · rintro ⟨hk, hki⟩
        exact ⟨by rw [hk, Fin.predAbove_castSucc_self], hki⟩
    rw [hset, hc, Fin.predAbove_castSucc_self]
    have hold := h.residual_nonpos i
    rw [hc] at hold
    refine le_trans (Finset.sum_le_sum fun k _ => ?_) hold
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left hle₁ (Nat.cast_nonneg _)) _
  by_cases hs : q i = p.succ
  · -- The right half: the whole left fibre is a negative offset.
    have hset : univ.filter (fun k => p.predAbove (q k) = p.predAbove (q i) ∧ k ≤ i) =
        fibre q p.castSucc ∪ univ.filter (fun k => q k = p.succ ∧ k ≤ i) := by
      ext k
      simp only [fibre, mem_filter, mem_univ, true_and, mem_union]
      rw [hs, Fin.predAbove_succ_self]
      constructor
      · rintro ⟨hk, hki⟩
        rcases (predAbove_eq_self_iff p (q k)).mp hk with hk' | hk'
        · exact Or.inl hk'
        · exact Or.inr ⟨hk', hki⟩
      · rintro (hk | ⟨hk, hki⟩)
        · refine ⟨by rw [hk, Fin.predAbove_castSucc_self], ?_⟩
          by_contra hki
          have := h.monotone (le_of_not_ge hki)
          rw [hk, hs] at this
          exact absurd this (not_le.mpr hcs)
        · exact ⟨by rw [hk, Fin.predAbove_succ_self], hki⟩
    have hdisj' : Disjoint (fibre q p.castSucc)
        (univ.filter (fun k => q k = p.succ ∧ k ≤ i)) := by
      rw [Finset.disjoint_filter]
      intro k _ hk hk'
      rw [hk] at hk'
      exact hcs.ne hk'.1
    rw [hset, hs, Fin.predAbove_succ_self, Finset.sum_union hdisj']
    set μ := fibreMean w r (fun k => p.predAbove (q k)) p
    have hleft : ∑ k ∈ fibre q p.castSucc, (r k - (w k : ℝ) * μ) =
        fibreWeight w q p.castSucc * fibreMean w r q p.castSucc -
          fibreWeight w q p.castSucc * μ := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hSc]
      rfl
    have hright : ∑ k ∈ univ.filter (fun k => q k = p.succ ∧ k ≤ i), (r k - (w k : ℝ) * μ) =
        ∑ k ∈ univ.filter (fun k => q k = p.succ ∧ k ≤ i),
            (r k - (w k : ℝ) * fibreMean w r q p.succ) +
          (∑ k ∈ univ.filter (fun k => q k = p.succ ∧ k ≤ i), (w k : ℝ)) *
            (fibreMean w r q p.succ - μ) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hpart : (∑ k ∈ univ.filter (fun k => q k = p.succ ∧ k ≤ i), (w k : ℝ)) ≤
        fibreWeight w q p.succ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k
        simp only [fibre, mem_filter, mem_univ, true_and]
        exact fun hk => hk.1
      · exact fun k _ _ => Nat.cast_nonneg _
    have hold := h.residual_nonpos i
    rw [hs] at hold
    have hprod := mul_le_mul_of_nonneg_right hpart (sub_nonneg.mpr hle₂)
    rw [hleft, hright]
    linarith
  · -- Away from the merged pair, fibres and means are unchanged.
    have hne : p.predAbove (q i) ≠ p := by
      intro hp'
      rcases (predAbove_eq_self_iff p (q i)).mp hp' with h' | h'
      · exact hc h'
      · exact hs h'
    have hiff : ∀ k, p.predAbove (q k) = p.predAbove (q i) ↔ q k = q i :=
      fun k => predAbove_eq_predAbove_iff p hne
    have hmean : fibreMean w r (fun k => p.predAbove (q k)) (p.predAbove (q i)) =
        fibreMean w r q (q i) := by
      unfold fibreMean fibreWeight fibre
      rw [Finset.filter_congr (fun k _ => hiff k)]
    rw [hmean, Finset.filter_congr (fun k _ => and_congr (hiff k) Iff.rfl)]
    exact h.residual_nonpos i

/-- Every pooling can be coarsened to a pooling with strictly decreasing fibre means. -/
theorem exists_strictAnti_pooling (hw : ∀ i, 0 < w i) :
    ∀ (m : ℕ) (q : Fin L → Fin m), IsPooling w r q →
      ∃ (m' : ℕ) (q' : Fin L → Fin m'), IsPooling w r q' ∧ StrictAnti (fibreMean w r q') := by
  intro m
  induction m with
  | zero =>
    intro q h
    exact ⟨0, q, h, fun a => a.elim0⟩
  | succ m ih =>
    intro q h
    by_cases hs : StrictAnti (fibreMean w r q)
    · exact ⟨_, q, h, hs⟩
    · cases m with
      | zero =>
        refine absurd ?_ hs
        intro a b hab
        have ha := a.isLt
        have hb := b.isLt
        rw [Fin.lt_def] at hab
        omega
      | succ m =>
        rw [Fin.strictAnti_iff_succ_lt] at hs
        push Not at hs
        obtain ⟨p, hp⟩ := hs
        exact ih _ (h.merge hw p hp)

end ParabolicConeExistence

open ParabolicConeExistence in
/-- Numerical existence of the block root/weight cone coarsening. -/
theorem glBlockConeExists : GLBlockConeExistenceStatement := by
  intro n B r
  obtain ⟨m, q, hq, ht⟩ :=
    exists_strictAnti_pooling (r := r) B.positive B.length (fun i => i) (isPooling_id B.positive)
  let C : BlockShape n :=
    { length := m
      size := fun j => ∑ i ∈ univ.filter (fun i => q i = j), B.size i
      positive := fun j => by
        obtain ⟨i, hi⟩ := hq.surjective j
        exact Finset.sum_pos (fun k _ => B.positive k) ⟨i, by simp [hi]⟩
      sum_eq := by rw [Finset.sum_fiberwise univ q B.size, B.sum_eq] }
  refine ⟨C, q, fibreMean B.size r q, hq.monotone, hq.surjective, fun j => rfl, ht,
    fun j => ?_, hq.residual_nonpos⟩
  change _ = ((∑ i ∈ univ.filter (fun i => q i = j), B.size i : ℕ) : ℝ) * _
  rw [Nat.cast_sum]
  exact sum_fibre_eq B.positive hq.surjective j

end Langlands
