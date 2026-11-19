import Langlands.Representation.Archimedean.CompoundMinorProduct
import Langlands.Representation.Archimedean.NestedFinsetFamilies
import Mathlib.Data.Fintype.Fin

/-! # Row occurrences in a compact model with paired coordinates -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.RealCompactRows

open Finset

variable {β γ : Type*}

/-- Two rows per rotation plane and one row per remaining coordinate. -/
abbrev Rows (β γ : Type*) := (β × Bool) ⊕ γ

/-- A permutation that exchanges the two coordinates in each selected pair. -/
def flip (δ : β → Bool) : Equiv.Perm (Rows β γ) :=
  let f : Rows β γ → Rows β γ
    | .inl (b, σ) => .inl (b, if δ b then !σ else σ)
    | .inr c => .inr c
  Function.Involutive.toPerm f (by
    intro a
    rcases a with ⟨b, σ⟩ | c
    · cases h : δ b <;> simp [f, h]
    · rfl)

@[simp] theorem flip_inl (δ : β → Bool) (b : β) (σ : Bool) :
    flip (γ := γ) δ (.inl (b, σ)) = .inl (b, if δ b then !σ else σ) :=
  rfl

@[simp] theorem flip_inr (δ : β → Bool) (c : γ) : flip δ (.inr c) = .inr c :=
  rfl

@[simp] theorem flip_symm (δ : β → Bool) :
    (flip (γ := γ) δ).symm = flip δ :=
  rfl

theorem flip_mul (δ ε : β → Bool) :
    flip (γ := γ) δ * flip ε = flip (fun b => xor (δ b) (ε b)) := by
  ext a
  rcases a with ⟨b, σ⟩ | c
  · simp only [Equiv.Perm.mul_apply, flip_inl]
    cases hd : δ b <;> cases he : ε b <;> simp [*]
  · simp

variable [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
variable (w : β → ℕ) (s : γ → ℕ)

/-- The number of levels used to realize every prescribed row occurrence. -/
def height : ℕ := (∑ b, w b) + ∑ c, s c

omit [DecidableEq β] [DecidableEq γ] in
private theorem weight_le_height (b : β) : w b ≤ height w s := by
  have h : w b ≤ ∑ i, w i := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ b)
  unfold height
  omega

omit [DecidableEq β] [DecidableEq γ] in
private theorem singleton_le_height (c : γ) : s c ≤ height w s := by
  have h : s c ≤ ∑ i, s i := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ c)
  unfold height
  omega

/-- The full weight goes on one row in each pair. -/
def count (ε : β → Bool) : Rows β γ → ℕ
  | .inl (b, σ) => if σ = ε b then w b else 0
  | .inr c => s c

/-- At each level take the rows whose prescribed count exceeds that level. -/
def targetRows (ε : β → Bool) (t : Fin (height w s)) : Finset (Rows β γ) :=
  univ.filter fun a => t.val < count w s ε a

omit [DecidableEq β] [DecidableEq γ] in
theorem targetRows_map_flip (δ ε : β → Bool) (t : Fin (height w s)) :
    (targetRows w s ε t).map (flip δ).toEmbedding =
      targetRows w s (fun b => if δ b then !(ε b) else ε b) t := by
  ext a
  rw [mem_map_equiv, flip_symm]
  simp only [targetRows, mem_filter, mem_univ, true_and]
  rcases a with ⟨b, σ⟩ | c
  · simp only [flip_inl]
    cases hd : δ b <;> cases he : ε b <;> cases σ <;> simp [count, *]
  · simp [count]

/-- The dimensions of the exterior factors are independent of the pair orientations. -/
def degree (t : Fin (height w s)) : ℕ := (targetRows w s (fun _ => true) t).card

omit [DecidableEq β] [DecidableEq γ] in
theorem card_targetRows (ε : β → Bool) (t : Fin (height w s)) :
    (targetRows w s ε t).card = degree w s t := by
  have h : (fun b => if !(ε b) then !true else true) = ε := by
    funext b
    cases ε b <;> rfl
  rw [← h, ← targetRows_map_flip w s (fun b => !(ε b)), card_map]
  rfl

/-- A configuration has one subset of the prescribed size at each level. -/
abbrev Configuration := CompoundMinorProduct.Selection (Rows β γ) (degree w s)

/-- The canonical configuration for the chosen orientation of every pair. -/
def target (ε : β → Bool) : Configuration w s :=
  fun t => ⟨targetRows w s ε t, card_targetRows w s ε t⟩

variable {w s}

/-- The number of subsets of a configuration containing a row. -/
def occurrence (q : Configuration w s) (a : Rows β γ) : ℕ :=
  (univ.filter fun t => a ∈ (q t).val).card

/-- The frequency on a rotation plane, positive on the `true` row. -/
def frequency (q : Configuration w s) (b : β) : ℤ :=
  (occurrence q (.inl (b, true)) : ℤ) - occurrence q (.inl (b, false))

theorem occurrence_target (ε : β → Bool) (a : Rows β γ) :
    occurrence (target w s ε) a = count w s ε a := by
  have h : count w s ε a ≤ height w s := by
    rcases a with ⟨b, σ⟩ | c
    · change (if σ = ε b then w b else 0) ≤ _
      split_ifs
      · exact weight_le_height w s b
      · exact Nat.zero_le _
    · exact singleton_le_height w s c
  have heq : (univ.filter fun t : Fin (height w s) => a ∈ (target w s ε t).val) =
      univ.filter (fun t : Fin (height w s) => t.val < count w s ε a) := by
    ext t
    simp [target, targetRows]
  rw [occurrence, heq, Fin.card_filter_val_lt, min_eq_right h]

theorem frequency_target (ε : β → Bool) (b : β) :
    frequency (target w s ε) b = if ε b then (w b : ℤ) else -(w b : ℤ) := by
  cases h : ε b <;> simp [frequency, occurrence_target, count, h]

theorem target_injective (hw : ∀ b, 0 < w b) :
    Function.Injective (target w s) := by
  intro ε ε' h
  funext b
  have hb := congrArg (fun q => frequency q b) h
  rw [frequency_target, frequency_target] at hb
  have hp := hw b
  cases h₁ : ε b <;> cases h₂ : ε' b <;> simp_all

private theorem sum_occurrence (q : Configuration w s) :
    (∑ a, occurrence q a) = ∑ t, degree w s t := by
  simp only [occurrence, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  exact sum_congr rfl fun t _ => by rw [← sum_filter, filter_mem_eq_inter, univ_inter,
    ← card_eq_sum_ones, (q t).property]

omit [DecidableEq β] [DecidableEq γ] in
private theorem sum_rows (f : Rows β γ → ℕ) :
    (∑ a, f a) =
      (∑ b, (f (.inl (b, true)) + f (.inl (b, false)))) + ∑ c, f (.inr c) := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp [add_comm]

private theorem total_degree :
    (∑ t, degree w s t) = (∑ b, w b) + ∑ c, s c := by
  rw [← sum_occurrence (target w s fun _ => true), sum_rows]
  simp [occurrence_target, count]

private theorem orient_pair {x y d : ℕ}
    (hlo : d ≤ ((x : ℤ) - y).natAbs) (hsum : x + y = d) :
    ∃ σ : Bool, x = (if true = σ then d else 0) ∧ y = (if false = σ then d else 0) := by
  by_cases h : y ≤ x
  · have he : (↑x : ℤ) - ↑y = ↑(((x : ℤ) - y).natAbs) :=
      (Int.natAbs_of_nonneg (by omega)).symm
    exact ⟨true, by simp; omega, by simp; omega⟩
  · have he : -((↑x : ℤ) - ↑y) = ↑(((x : ℤ) - y).natAbs) := by
      rw [← Int.natAbs_neg ((x : ℤ) - y), Int.natAbs_of_nonneg (by omega)]
    exact ⟨false, by simp; omega, by simp; omega⟩

/-- The rotation and singleton lower bounds saturate the total number of rows. The resulting
counts determine the entire configuration because the canonical sets are nested. -/
theorem exists_eq_target (q : Configuration w s)
    (hw : ∀ b, w b ≤ (frequency q b).natAbs)
    (hs : ∀ c, s c ≤ occurrence q (.inr c)) :
    ∃ ε, q = target w s ε := by
  let pairCount (b : β) := occurrence q (.inl (b, true)) + occurrence q (.inl (b, false))
  have hpair (b : β) : w b ≤ pairCount b := by
    refine (hw b).trans ?_
    unfold frequency pairCount
    exact (Int.natAbs_sub_le _ _).trans (by simp)
  have htotal := (sum_occurrence q).trans total_degree
  rw [sum_rows] at htotal
  change (∑ b, pairCount b) + ∑ c, occurrence q (.inr c) =
    (∑ b, w b) + ∑ c, s c at htotal
  have hsum₁ : (∑ b, w b) ≤ ∑ b, pairCount b := sum_le_sum fun b _ => hpair b
  have hsum₂ : (∑ c, s c) ≤ ∑ c, occurrence q (.inr c) := sum_le_sum fun c _ => hs c
  have heq₁ : (∑ b, w b) = ∑ b, pairCount b := by omega
  have heq₂ : (∑ c, s c) = ∑ c, occurrence q (.inr c) := by omega
  have h₁ (b : β) : pairCount b = w b := by
    refine le_antisymm ?_ (hpair b)
    by_contra! hb
    exact (not_lt_of_ge heq₁.ge) (sum_lt_sum (fun i _ => hpair i) ⟨b, mem_univ b, hb⟩)
  have h₂ (c : γ) : occurrence q (.inr c) = s c := by
    refine le_antisymm ?_ (hs c)
    by_contra! hc
    exact (not_lt_of_ge heq₂.ge) (sum_lt_sum (fun i _ => hs i) ⟨c, mem_univ c, hc⟩)
  choose ε he using fun b => orient_pair (hw b) (h₁ b)
  refine ⟨ε, ?_⟩
  have hsets := eq_antitone_of_card_of_occurrences (fun t => (q t).val)
    (targetRows w s ε) (fun _ _ htt _ ha => by
      simp only [targetRows, mem_filter, mem_univ, true_and] at ha ⊢
      exact lt_of_le_of_lt htt ha)
    (fun t => (q t).property.trans (card_targetRows w s ε t).symm)
    (fun a => by
      change occurrence q a = occurrence (target w s ε) a
      rw [occurrence_target]
      rcases a with ⟨b, σ⟩ | c
      · cases σ
        · exact (he b).2
        · exact (he b).1
      · exact h₂ c)
  exact funext fun t => Subtype.ext (congrFun hsets t)

end Langlands.Archimedean.RealCompactRows
