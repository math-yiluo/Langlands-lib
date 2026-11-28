import Langlands.Representation.Unramified.MinusculeCosets
import Langlands.Representation.Shahidi.Geometry
import Langlands.Representation.RankinSelberg.TwoBlockDominantBlockSupport
import Langlands.Representation.RankinSelberg.UnramifiedWhittakerCells

/-! # Splitting minuscule coset representatives along two blocks

A subset `S` of `Fin (m + n)` is the pair of its parts `S₁ ⊆ Fin m` and `S₂ ⊆ Fin n`. Sums over
the subsets of a given size and products over `S` split along the two parts, and the radical
pairs of `S` (`i ∈ S`, `j ∉ S`, `i < j`) are those of `S₁`, those of `S₂`, and the
`|S₁| (n - |S₂|)` pairs across the blocks. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

open Langlands.GeneralLinear Langlands.GeneralLinear.Iwasawa Langlands.Unramified.MinusculeCosets

section Subsets

variable {m n : ℕ}

/-- The part of a subset of `Fin (m + n)` in the first block. -/
def firstPart (S : Finset (Fin (m + n))) : Finset (Fin m) :=
  Finset.univ.filter fun i => Fin.castAdd n i ∈ S

/-- The part of a subset of `Fin (m + n)` in the second block. -/
def secondPart (S : Finset (Fin (m + n))) : Finset (Fin n) :=
  Finset.univ.filter fun j => Fin.natAdd m j ∈ S

@[simp] theorem mem_firstPart {S : Finset (Fin (m + n))} {i : Fin m} :
    i ∈ firstPart S ↔ Fin.castAdd n i ∈ S := by
  simp [firstPart]

@[simp] theorem mem_secondPart {S : Finset (Fin (m + n))} {j : Fin n} :
    j ∈ secondPart S ↔ Fin.natAdd m j ∈ S := by
  simp [secondPart]

/-- The subset of `Fin (m + n)` with parts `S₁` and `S₂`. -/
def joinParts (S₁ : Finset (Fin m)) (S₂ : Finset (Fin n)) : Finset (Fin (m + n)) :=
  (S₁.disjSum S₂).map finSumFinEquiv.toEmbedding

@[simp] theorem castAdd_mem_joinParts {S₁ : Finset (Fin m)} {S₂ : Finset (Fin n)} {i : Fin m} :
    Fin.castAdd n i ∈ joinParts S₁ S₂ ↔ i ∈ S₁ := by
  simp [joinParts, Finset.mem_map_equiv]

@[simp] theorem natAdd_mem_joinParts {S₁ : Finset (Fin m)} {S₂ : Finset (Fin n)} {j : Fin n} :
    Fin.natAdd m j ∈ joinParts S₁ S₂ ↔ j ∈ S₂ := by
  simp [joinParts, Finset.mem_map_equiv]

/-- Subsets of `Fin (m + n)` are pairs of subsets of `Fin m` and `Fin n`. -/
def splitEquiv : Finset (Fin (m + n)) ≃ Finset (Fin m) × Finset (Fin n) where
  toFun S := (firstPart S, secondPart S)
  invFun p := joinParts p.1 p.2
  left_inv S := by
    ext i
    induction i using Fin.addCases <;> simp
  right_inv p := by
    ext i <;> simp

theorem card_eq_card_firstPart_add (S : Finset (Fin (m + n))) :
    S.card = (firstPart S).card + (secondPart S).card := by
  classical
  have h : ∀ T : Finset (Fin (m + n)), T.card = ∑ i : Fin (m + n), if i ∈ T then 1 else 0 := by
    intro T
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id]
  have h₁ : (firstPart S).card = ∑ i : Fin m, if Fin.castAdd n i ∈ S then 1 else 0 := by
    rw [Finset.sum_boole, Nat.cast_id]
    rfl
  have h₂ : (secondPart S).card = ∑ j : Fin n, if Fin.natAdd m j ∈ S then 1 else 0 := by
    rw [Finset.sum_boole, Nat.cast_id]
    rfl
  rw [h S, Fin.sum_univ_add, h₁, h₂]

theorem sum_subtype_eq_sum_ite {α R : Type*} [Fintype α] [AddCommMonoid R] (P : α → Prop)
    [DecidablePred P] (f : α → R) :
    ∑ a : Subtype P, f a.1 = ∑ a, if P a then f a else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm

/-- **Sums over subsets of a fixed size, split along the two blocks.** -/
theorem sum_card_eq_split {R : Type*} [AddCommMonoid R] (k : ℕ)
    (φ : Finset (Fin m) → Finset (Fin n) → R) :
    ∑ S : {S : Finset (Fin (m + n)) // S.card = k}, φ (firstPart S.1) (secondPart S.1) =
      ∑ p ∈ Finset.antidiagonal k, ∑ S₁ : {S₁ : Finset (Fin m) // S₁.card = p.1},
        ∑ S₂ : {S₂ : Finset (Fin n) // S₂.card = p.2}, φ S₁.1 S₂.1 := by
  classical
  rw [sum_subtype_eq_sum_ite (fun S : Finset (Fin (m + n)) => S.card = k)
    (fun S => φ (firstPart S) (secondPart S))]
  have hR : ∀ p : ℕ × ℕ, ∑ S₁ : {S₁ : Finset (Fin m) // S₁.card = p.1},
      ∑ S₂ : {S₂ : Finset (Fin n) // S₂.card = p.2}, φ S₁.1 S₂.1 =
        ∑ S₁ : Finset (Fin m), ∑ S₂ : Finset (Fin n),
          if S₁.card = p.1 ∧ S₂.card = p.2 then φ S₁ S₂ else 0 := by
    intro p
    rw [sum_subtype_eq_sum_ite (fun S₁ : Finset (Fin m) => S₁.card = p.1)
      (fun S₁ => ∑ S₂ : {S₂ : Finset (Fin n) // S₂.card = p.2}, φ S₁ S₂.1)]
    refine Finset.sum_congr rfl fun S₁ _ => ?_
    rw [sum_subtype_eq_sum_ite (fun S₂ : Finset (Fin n) => S₂.card = p.2) (fun S₂ => φ S₁ S₂)]
    split_ifs with h1
    · exact Finset.sum_congr rfl fun S₂ _ => by simp [h1]
    · exact (Finset.sum_eq_zero fun S₂ _ => by simp [h1]).symm
  simp only [hR]
  rw [← (splitEquiv (m := m) (n := n)).symm.sum_comp, Fintype.sum_prod_type]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S₁ _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S₂ _ => ?_
  change (if (joinParts S₁ S₂).card = k then
      φ (firstPart (joinParts S₁ S₂)) (secondPart (joinParts S₁ S₂)) else 0) = _
  have e₁ : firstPart (joinParts S₁ S₂) = S₁ := by ext i; simp
  have e₂ : secondPart (joinParts S₁ S₂) = S₂ := by ext i; simp
  rw [card_eq_card_firstPart_add, e₁, e₂]
  rw [← Finset.sum_filter]
  have hfilt : (Finset.antidiagonal k).filter (fun p : ℕ × ℕ => S₁.card = p.1 ∧ S₂.card = p.2) =
      if S₁.card + S₂.card = k then {(S₁.card, S₂.card)} else ∅ := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_antidiagonal]
    split_ifs with h
    · simp only [Finset.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨_, rfl, rfl⟩
        exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, rfl⟩
        exact ⟨h, rfl, rfl⟩
    · simp only [Finset.notMem_empty, iff_false, not_and]
      rintro hab rfl rfl
      exact h hab
  rw [hfilt]
  split_ifs <;> simp

/-- A product over a subset of `Fin (m + n)` is the product over its two parts. -/
theorem prod_mem_split {M : Type*} [CommMonoid M] (S : Finset (Fin (m + n)))
    (χ : Fin (m + n) → M) :
    ∏ j ∈ S, χ j =
      (∏ i ∈ firstPart S, χ (Fin.castAdd n i)) * ∏ j ∈ secondPart S, χ (Fin.natAdd m j) := by
  classical
  rw [firstPart, secondPart, Finset.prod_filter, Finset.prod_filter,
    ← Fin.prod_univ_add (f := fun j => if j ∈ S then χ j else 1),
    ← Finset.prod_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-! ### Radical pairs along the two blocks -/

theorem isRadicalPair_castAdd_castAdd {S : Finset (Fin (m + n))} {i j : Fin m} :
    IsRadicalPair S (Fin.castAdd n i) (Fin.castAdd n j) ↔ IsRadicalPair (firstPart S) i j := by
  simp only [IsRadicalPair, mem_firstPart, Fin.lt_def, Fin.val_castAdd]

theorem isRadicalPair_natAdd_natAdd {S : Finset (Fin (m + n))} {i j : Fin n} :
    IsRadicalPair S (Fin.natAdd m i) (Fin.natAdd m j) ↔ IsRadicalPair (secondPart S) i j := by
  simp only [IsRadicalPair, mem_secondPart, Fin.lt_def, Fin.val_natAdd, Nat.add_lt_add_iff_left]

theorem isRadicalPair_castAdd_natAdd {S : Finset (Fin (m + n))} {i : Fin m} {j : Fin n} :
    IsRadicalPair S (Fin.castAdd n i) (Fin.natAdd m j) ↔ i ∈ firstPart S ∧ j ∉ secondPart S := by
  simp only [IsRadicalPair, mem_firstPart, mem_secondPart, Fin.lt_def, Fin.val_castAdd,
    Fin.val_natAdd]
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · exact fun h => ⟨h.1, h.2, by omega⟩

theorem not_isRadicalPair_natAdd_castAdd {S : Finset (Fin (m + n))} (i : Fin n) (j : Fin m) :
    ¬ IsRadicalPair S (Fin.natAdd m i) (Fin.castAdd n j) := by
  simp only [IsRadicalPair, Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
  omega

theorem card_radicalPairs_eq_sum {k : ℕ} (S : Finset (Fin k)) :
    Fintype.card (RadicalPairs S) =
      ∑ a : Fin k, ∑ b : Fin k, if IsRadicalPair S a b then 1 else 0 := by
  classical
  rw [Fintype.card_subtype, Finset.card_filter, ← Fintype.sum_prod_type']

/-- **Radical pairs split along the two blocks**: those inside each block, and the
`|S₁| (n - |S₂|)` pairs from the first block in `S` to the second block off `S`. -/
theorem card_radicalPairs_split (S : Finset (Fin (m + n))) :
    Fintype.card (RadicalPairs S) = Fintype.card (RadicalPairs (firstPart S)) +
      Fintype.card (RadicalPairs (secondPart S)) +
        (firstPart S).card * (n - (secondPart S).card) := by
  classical
  rw [card_radicalPairs_eq_sum, card_radicalPairs_eq_sum, card_radicalPairs_eq_sum,
    Fin.sum_univ_add]
  simp_rw [Fin.sum_univ_add]
  simp only [isRadicalPair_castAdd_castAdd, isRadicalPair_natAdd_natAdd,
    isRadicalPair_castAdd_natAdd, not_isRadicalPair_natAdd_castAdd, ite_false,
    Finset.sum_const_zero, zero_add]
  have hB : ∑ j : Fin n, (if j ∉ secondPart S then 1 else 0) = n - (secondPart S).card := by
    rw [← Finset.card_filter]
    rw [show Finset.univ.filter (fun j => j ∉ secondPart S) = (secondPart S)ᶜ by ext; simp,
      Finset.card_compl, Fintype.card_fin]
  have hc : ∀ i : Fin m, ∑ j : Fin n, (if i ∈ firstPart S ∧ j ∉ secondPart S then 1 else 0) =
      if i ∈ firstPart S then n - (secondPart S).card else 0 := by
    intro i
    split_ifs with hi
    · simp only [hi, true_and]
      exact hB
    · simp [hi]
  simp only [Finset.sum_add_distrib, hc]
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, Finset.filter_mem_eq_inter,
    Finset.univ_inter]
  ring

end Subsets

end Langlands.Shahidi.OpenCell
