import Langlands.LinearAlgebra.ChainCoxeterMinors

/-! # The modified chain in path indexing -/

namespace Langlands.LinearAlgebra.ChainCoxeter

open Matrix

variable {R : Type*} [CommRing R]

section Equiv

variable {L i : ℕ}

/-- The splitting of the path vertices `Fin (L + 1)` into the left part `0, …, i`, the right part
`i + 2, …, L` and the middle vertex `i + 1`. -/
def skipEquiv (hi : i + 2 ≤ L) : (Fin (i + 1) ⊕ Fin (L - i - 2 + 1)) ⊕ Unit ≃ Fin (L + 1) where
  toFun v := match v with
    | Sum.inl (Sum.inl a) => ⟨a, by omega⟩
    | Sum.inl (Sum.inr b) => ⟨i + 2 + b, by omega⟩
    | Sum.inr _ => ⟨i + 1, by omega⟩
  invFun r :=
    if h : (r : ℕ) ≤ i then Sum.inl (Sum.inl ⟨r, by omega⟩)
    else if (r : ℕ) = i + 1 then Sum.inr ()
    else Sum.inl (Sum.inr ⟨r - (i + 2), by omega⟩)
  left_inv v := by
    rcases v with (a | b) | u
    · simp [show (a : ℕ) ≤ i by omega]
    · have h1 : ¬(i + 2 + (b : ℕ) ≤ i) := by omega
      have h2 : ¬(i + 2 + (b : ℕ) = i + 1) := by omega
      simp only [h1, h2, dite_false, ite_false, Sum.inl.injEq, Sum.inr.injEq]
      ext; simp
    · simp
  right_inv r := by
    by_cases h : (r : ℕ) ≤ i
    · simp [h]
    · by_cases h' : (r : ℕ) = i + 1
      · simp [h']; ext; simp [h']
      · simp only [h, h', dite_false, ite_false]
        ext; simp; omega

@[simp] theorem skipEquiv_inl_inl (hi : i + 2 ≤ L) (a : Fin (i + 1)) :
    ((skipEquiv hi (Sum.inl (Sum.inl a)) : Fin (L + 1)) : ℕ) = a := rfl

@[simp] theorem skipEquiv_inl_inr (hi : i + 2 ≤ L) (b : Fin (L - i - 2 + 1)) :
    ((skipEquiv hi (Sum.inl (Sum.inr b)) : Fin (L + 1)) : ℕ) = i + 2 + b := rfl

@[simp] theorem skipEquiv_inr (hi : i + 2 ≤ L) (u : Unit) :
    ((skipEquiv hi (Sum.inr u) : Fin (L + 1)) : ℕ) = i + 1 := rfl

end Equiv

section Embedding

variable {r r' : ℕ} {a b : R}

/-- Restricting a chain factor along an injective map of vertices that carries the edge `j'` to
the edge `j` gives a chain factor at `j'`. -/
theorem IsChainFactor.submatrix_of_embedding {g : Matrix (Fin (r + 1)) (Fin (r + 1)) R}
    {j : Fin r}
    (h : IsChainFactor g j a b) (φ : Fin (r' + 1) → Fin (r + 1)) (hφ : Function.Injective φ)
    (j' : Fin r') (h₁ : φ j'.castSucc = j.castSucc) (h₂ : φ j'.succ = j.succ) :
    IsChainFactor (g.submatrix φ φ) j' a b where
  apply_of_ne x c hc₁ hc₂ := by
    simp only [submatrix_apply]
    rw [h.apply_of_ne _ _ (by rw [← h₁]; exact fun e => hc₁ (hφ e))
      (by rw [← h₂]; exact fun e => hc₂ (hφ e))]
    simp [one_apply, hφ.eq_iff]
  apply_succ x := by
    simp only [submatrix_apply]
    rw [h₂, h.apply_succ, ← h₁]
    simp only [hφ.eq_iff]
  apply_succ_castSucc := by
    simp only [submatrix_apply]
    rw [h₁, h₂]; exact h.apply_succ_castSucc
  apply_castSucc_of_ne x hx₁ hx₂ := by
    simp only [submatrix_apply]
    rw [h₁]
    exact h.apply_castSucc_of_ne _ (by rw [← h₁]; exact fun e => hx₁ (hφ e))
      (by rw [← h₂]; exact fun e => hx₂ (hφ e))

/-- Restricting a chain factor to vertices avoiding its edge gives the identity. -/
theorem IsChainFactor.submatrix_eq_one {g : Matrix (Fin (r + 1)) (Fin (r + 1)) R} {j : Fin r}
    (h : IsChainFactor g j a b) {ι : Type*} [DecidableEq ι] (φ : ι → Fin (r + 1))
    (hφ : Function.Injective φ) (h₁ : ∀ x, φ x ≠ j.castSucc) (h₂ : ∀ x, φ x ≠ j.succ) :
    g.submatrix φ φ = 1 := by
  ext x c
  simp only [submatrix_apply]
  rw [h.apply_of_ne _ _ (h₁ c) (h₂ c)]
  simp [one_apply, hφ.eq_iff]

end Embedding

section Skip

variable {L i : ℕ} (hi : i + 2 ≤ L)

/-- The skip factor of the full chain `Fin (L + 1)`: it fixes every basis vector other than
`e_i` and `e_{i+2}`, sends `e_{i+2}` to `lam • e_i`, and sends `e_i` into the span of `e_i` and
`e_{i+2}` with coefficient `mu` on `e_{i+2}`. -/
structure IsSkipFactor (g : Matrix (Fin (L + 1)) (Fin (L + 1)) R) (lam mu : R) : Prop where
  apply_of_ne : ∀ x c : Fin (L + 1), (c : ℕ) ≠ i → (c : ℕ) ≠ i + 2 →
    g x c = (1 : Matrix _ _ R) x c
  apply_right : ∀ x : Fin (L + 1), g x ⟨i + 2, by omega⟩ = if (x : ℕ) = i then lam else 0
  apply_right_left : g ⟨i + 2, by omega⟩ ⟨i, by omega⟩ = mu
  apply_left_of_ne : ∀ x : Fin (L + 1), (x : ℕ) ≠ i → (x : ℕ) ≠ i + 2 →
    g x ⟨i, by omega⟩ = 0

/-- A list of chain factors of the full chain in which every edge other than `i` and `i + 1`
occurs exactly once, the edges `i` and `i + 1` do not occur, and every other factor is the
identity. -/
structure IsChainListSkip {ι : Type*} (i : ℕ) (l : List ι)
    (F : ι → Matrix (Fin (L + 1)) (Fin (L + 1)) R)
    (E : ι → Option (Fin L)) (a b : Fin L → R) : Prop where
  eq_one : ∀ x ∈ l, E x = none → F x = 1
  isChainFactor : ∀ x ∈ l, ∀ j, E x = some j → IsChainFactor (F x) j (a j) (b j)
  countP_eq_one : ∀ j : Fin L, (j : ℕ) ≠ i → (j : ℕ) ≠ i + 1 →
    l.countP (fun x => E x = some j) = 1
  countP_eq_zero : ∀ j : Fin L, (j : ℕ) = i ∨ (j : ℕ) = i + 1 →
    l.countP (fun x => E x = some j) = 0

end Skip

theorem IsChainFactor.apply_of_not_mem {r : ℕ} {a b : R} {g : Matrix (Fin (r + 1)) (Fin (r + 1)) R}
    {j : Fin r} (h : IsChainFactor g j a b) {x c : Fin (r + 1)}
    (hxc : ¬((x = j.castSucc ∨ x = j.succ) ∧ (c = j.castSucc ∨ c = j.succ))) :
    g x c = (1 : Matrix _ _ R) x c := by
  by_cases hc : c = j.castSucc ∨ c = j.succ
  · have hx : ¬(x = j.castSucc ∨ x = j.succ) := fun hx => hxc ⟨hx, hc⟩
    push Not at hx
    exact h.apply_row_of_ne hx.1 hx.2 c
  · push Not at hc
    exact h.apply_of_ne x c hc.1 hc.2

section Blocks

variable {L i : ℕ} (hi : i + 2 ≤ L)

/-- The left vertices `0, …, i`. -/
def skipLeft (a : Fin (i + 1)) : Fin (L + 1) := skipEquiv hi (Sum.inl (Sum.inl a))

/-- The right vertices `i + 2, …, L`. -/
def skipRight (b : Fin (L - i - 2 + 1)) : Fin (L + 1) := skipEquiv hi (Sum.inl (Sum.inr b))

/-- The left and right vertices together. -/
def skipOuter (w : Fin (i + 1) ⊕ Fin (L - i - 2 + 1)) : Fin (L + 1) := skipEquiv hi (Sum.inl w)

theorem skipLeft_injective : Function.Injective (skipLeft hi) :=
  fun _ _ h => Sum.inl_injective (Sum.inl_injective ((skipEquiv hi).injective h))

theorem skipRight_injective : Function.Injective (skipRight hi) :=
  fun _ _ h => Sum.inr_injective (Sum.inl_injective ((skipEquiv hi).injective h))

theorem skipOuter_injective : Function.Injective (skipOuter hi) :=
  fun _ _ h => Sum.inl_injective ((skipEquiv hi).injective h)

/-- A matrix agreeing with the identity outside the left block is block diagonal, with identity
right and middle blocks. -/
theorem submatrix_skipEquiv_of_left (X : Matrix (Fin (L + 1)) (Fin (L + 1)) R)
    (hX : ∀ x c : Fin (L + 1), ¬((x : ℕ) ≤ i ∧ (c : ℕ) ≤ i) → X x c = (1 : Matrix _ _ R) x c) :
    X.submatrix (skipEquiv hi) (skipEquiv hi) =
      fromBlocks (fromBlocks (X.submatrix (skipLeft hi) (skipLeft hi)) 0 0 1) 0 0 1 := by
  have hone : ∀ v w, ¬(((skipEquiv hi v : Fin (L + 1)) : ℕ) ≤ i ∧
      ((skipEquiv hi w : Fin (L + 1)) : ℕ) ≤ i) →
      X (skipEquiv hi v) (skipEquiv hi w) = (1 : Matrix _ _ R) v w := by
    intro v w hvw
    rw [hX _ _ hvw]
    simp [one_apply, (skipEquiv hi).injective.eq_iff]
  ext v w
  rcases v with (a | b) | u <;> rcases w with (a' | b') | u'
  · rfl
  all_goals
    rw [submatrix_apply, hone _ _ (by
      simp only [skipEquiv_inl_inl, skipEquiv_inl_inr, skipEquiv_inr]; omega)]
    simp [one_apply]

/-- A matrix agreeing with the identity outside the right block. -/
theorem submatrix_skipEquiv_of_right (X : Matrix (Fin (L + 1)) (Fin (L + 1)) R)
    (hX : ∀ x c : Fin (L + 1), ¬(i + 2 ≤ (x : ℕ) ∧ i + 2 ≤ (c : ℕ)) →
      X x c = (1 : Matrix _ _ R) x c) :
    X.submatrix (skipEquiv hi) (skipEquiv hi) =
      fromBlocks (fromBlocks 1 0 0 (X.submatrix (skipRight hi) (skipRight hi))) 0 0 1 := by
  have hone : ∀ v w, ¬(i + 2 ≤ ((skipEquiv hi v : Fin (L + 1)) : ℕ) ∧
      i + 2 ≤ ((skipEquiv hi w : Fin (L + 1)) : ℕ)) →
      X (skipEquiv hi v) (skipEquiv hi w) = (1 : Matrix _ _ R) v w := by
    intro v w hvw
    rw [hX _ _ hvw]
    simp [one_apply, (skipEquiv hi).injective.eq_iff]
  ext v w
  rcases v with (a | b) | u <;> rcases w with (a' | b') | u'
  pick_goal 5
  · rfl
  all_goals
    rw [submatrix_apply, hone _ _ (by
      simp only [skipEquiv_inl_inl, skipEquiv_inl_inr, skipEquiv_inr]; omega)]
    simp [one_apply]

/-- A matrix fixing the middle vertex and preserving the other vertices. -/
theorem submatrix_skipEquiv_of_outer (X : Matrix (Fin (L + 1)) (Fin (L + 1)) R)
    (hX : ∀ x c : Fin (L + 1), ((x : ℕ) = i + 1 ∨ (c : ℕ) = i + 1) →
      X x c = (1 : Matrix _ _ R) x c) :
    X.submatrix (skipEquiv hi) (skipEquiv hi) =
      fromBlocks (X.submatrix (skipOuter hi) (skipOuter hi)) 0 0 1 := by
  ext v w
  rcases v with v | u <;> rcases w with w | u'
  · rfl
  all_goals
    rw [submatrix_apply, hX _ _ (by simp)]
    simp [one_apply, (skipEquiv hi).injective.eq_iff]

theorem submatrix_skipEquiv_prod {ι : Type*} (l : List ι)
    (F : ι → Matrix (Fin (L + 1)) (Fin (L + 1)) R)
    (FL : ι → Matrix (Fin (i + 1)) (Fin (i + 1)) R)
    (FR : ι → Matrix (Fin (L - i - 2 + 1)) (Fin (L - i - 2 + 1)) R)
    (h : ∀ x ∈ l, (F x).submatrix (skipEquiv hi) (skipEquiv hi) =
      fromBlocks (fromBlocks (FL x) 0 0 (FR x)) 0 0 1) :
    (l.map F).prod.submatrix (skipEquiv hi) (skipEquiv hi) =
      fromBlocks (fromBlocks (l.map FL).prod 0 0 (l.map FR).prod) 0 0 1 := by
  induction l with
  | nil => simp [submatrix_one_equiv, fromBlocks_one]
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, ← submatrix_mul_equiv _ _ _ (skipEquiv hi),
      h x List.mem_cons_self, ih fun y hy => h y (List.mem_cons_of_mem x hy)]
    simp [fromBlocks_multiply]

end Blocks

section Transfer

variable {L i : ℕ} (hi : i + 2 ≤ L)

theorem skipOuter_val_eq_left_iff (w : Fin (i + 1) ⊕ Fin (L - i - 2 + 1)) :
    ((skipOuter hi w : Fin (L + 1)) : ℕ) = i ↔ w = Sum.inl (Fin.last i) := by
  rcases w with a | b
  · simp only [skipOuter, skipEquiv_inl_inl, Sum.inl.injEq, Fin.ext_iff, Fin.val_last]
  · simp only [skipOuter, skipEquiv_inl_inr, reduceCtorEq, iff_false]; omega

theorem skipOuter_val_eq_right_iff (w : Fin (i + 1) ⊕ Fin (L - i - 2 + 1)) :
    ((skipOuter hi w : Fin (L + 1)) : ℕ) = i + 2 ↔ w = Sum.inr 0 := by
  rcases w with a | b
  · simp only [skipOuter, skipEquiv_inl_inl, reduceCtorEq, iff_false]; omega
  · simp only [skipOuter, skipEquiv_inl_inr, Sum.inr.injEq, Fin.ext_iff, Fin.val_zero]; omega

variable {g : Matrix (Fin (L + 1)) (Fin (L + 1)) R} {lam mu : R}

theorem IsSkipFactor.apply_of_middle (hg : IsSkipFactor hi g lam mu) (x c : Fin (L + 1))
    (h : (x : ℕ) = i + 1 ∨ (c : ℕ) = i + 1) : g x c = (1 : Matrix _ _ R) x c := by
  by_cases hc₁ : (c : ℕ) = i
  · have hx : (x : ℕ) = i + 1 := by omega
    have hc : c = ⟨i, by omega⟩ := Fin.ext hc₁
    rw [hc, hg.apply_left_of_ne x (by omega) (by omega), one_apply_ne (fun e => by
      rw [e] at hx; simp at hx)]
  · by_cases hc₂ : (c : ℕ) = i + 2
    · have hx : (x : ℕ) = i + 1 := by omega
      have hc : c = ⟨i + 2, by omega⟩ := Fin.ext hc₂
      rw [hc, hg.apply_right x, ite_eq_right (by omega), one_apply_ne (fun e => by
        rw [e] at hx; simp at hx)]
    · exact hg.apply_of_ne x c hc₁ hc₂

theorem IsSkipFactor.submatrix_skipEquiv (hg : IsSkipFactor hi g lam mu) :
    g.submatrix (skipEquiv hi) (skipEquiv hi) =
      fromBlocks (g.submatrix (skipOuter hi) (skipOuter hi)) 0 0 1 :=
  submatrix_skipEquiv_of_outer hi g (hg.apply_of_middle hi)

theorem IsSkipFactor.isMergedFactor (hg : IsSkipFactor hi g lam mu) :
    IsMergedFactor (p := i) (q := L - i - 2) (g.submatrix (skipOuter hi) (skipOuter hi))
      lam mu where
  apply_of_ne w c hc₁ hc₂ := by
    simp only [submatrix_apply]
    rw [hg.apply_of_ne _ _ (fun h => hc₁ ((skipOuter_val_eq_left_iff hi c).mp h))
      (fun h => hc₂ ((skipOuter_val_eq_right_iff hi c).mp h))]
    simp [one_apply, (skipOuter_injective hi).eq_iff]
  apply_inr_zero w := by
    simp only [submatrix_apply]
    have h0 : skipOuter hi (Sum.inr 0) = ⟨i + 2, by omega⟩ := Fin.ext (by simp [skipOuter])
    rw [h0, hg.apply_right]
    simp only [skipOuter_val_eq_left_iff]
  apply_inr_zero_inl_last := by
    simp only [submatrix_apply]
    have h0 : skipOuter hi (Sum.inr 0) = ⟨i + 2, by omega⟩ := Fin.ext (by simp [skipOuter])
    have h1 : skipOuter hi (Sum.inl (Fin.last i)) = ⟨i, by omega⟩ := Fin.ext (by simp [skipOuter])
    rw [h0, h1]
    exact hg.apply_right_left
  apply_inl_last_of_ne w hw₁ hw₂ := by
    simp only [submatrix_apply]
    have h1 : skipOuter hi (Sum.inl (Fin.last i)) = ⟨i, by omega⟩ := Fin.ext (by simp [skipOuter])
    rw [h1]
    exact hg.apply_left_of_ne _ (fun h => hw₁ ((skipOuter_val_eq_left_iff hi w).mp h))
      (fun h => hw₂ ((skipOuter_val_eq_right_iff hi w).mp h))

end Transfer

section Lists

variable {L i : ℕ} (hi : i + 2 ≤ L)

/-- Keep the edges of the left chain. -/
def leftEdge (o : Option (Fin L)) : Option (Fin i) :=
  o.bind fun j => if h : (j : ℕ) < i then some ⟨j, h⟩ else none

theorem leftEdge_eq_some {o : Option (Fin L)} {j : Fin i} :
    leftEdge o = some j ↔ o = some ⟨j, by omega⟩ := by
  cases o with
  | none => simp [leftEdge]
  | some k =>
    by_cases hk : (k : ℕ) < i
    · simp only [leftEdge, Option.bind_some, hk, dite_true, Option.some.injEq, Fin.ext_iff]
    · simp only [leftEdge, Option.bind_some, hk, dite_false, reduceCtorEq, false_iff,
        Option.some.injEq]
      intro e; rw [e] at hk; simp at hk

/-- Keep the edges of the right chain, renumbered from `0`. -/
def rightEdge (o : Option (Fin L)) : Option (Fin (L - i - 2)) :=
  o.bind fun j => if h : i + 2 ≤ (j : ℕ) then some ⟨j - (i + 2), by have := j.2; omega⟩ else none

theorem rightEdge_eq_some {o : Option (Fin L)} {j : Fin (L - i - 2)} :
    rightEdge hi o = some j ↔ o = some ⟨i + 2 + j, by omega⟩ := by
  cases o with
  | none => simp [rightEdge]
  | some k =>
    by_cases hk : i + 2 ≤ (k : ℕ)
    · simp only [rightEdge, Option.bind_some, hk, dite_true, Option.some.injEq, Fin.ext_iff]
      omega
    · simp only [rightEdge, Option.bind_some, hk, dite_false, reduceCtorEq, false_iff,
        Option.some.injEq]
      intro e; rw [e] at hk; simp at hk

variable {ι : Type*} {l : List ι} {F : ι → Matrix (Fin (L + 1)) (Fin (L + 1)) R}
  {E : ι → Option (Fin L)} {a b : Fin L → R}

theorem IsChainListSkip.edge_ne (h : IsChainListSkip i l F E a b) {x : ι} (hx : x ∈ l)
    {j : Fin L} (hE : E x = some j) : (j : ℕ) ≠ i ∧ (j : ℕ) ≠ i + 1 := by
  constructor <;> intro hj <;>
  · have h0 := h.countP_eq_zero j (by omega)
    rw [List.countP_eq_zero] at h0
    exact h0 x hx (by simp [hE])

theorem IsChainListSkip.submatrix_skipEquiv (h : IsChainListSkip i l F E a b) {x : ι}
    (hx : x ∈ l) :
    (F x).submatrix (skipEquiv hi) (skipEquiv hi) =
      fromBlocks (fromBlocks ((F x).submatrix (skipLeft hi) (skipLeft hi)) 0 0
        ((F x).submatrix (skipRight hi) (skipRight hi))) 0 0 1 := by
  cases hE : E x with
  | none =>
    rw [h.eq_one x hx hE, submatrix_one_equiv, submatrix_one _ (skipLeft_injective hi),
      submatrix_one _ (skipRight_injective hi), fromBlocks_one, fromBlocks_one]
  | some j =>
    have hj := h.edge_ne hx hE
    have hg := h.isChainFactor x hx j hE
    by_cases hlt : (j : ℕ) < i
    · have hR : (F x).submatrix (skipRight hi) (skipRight hi) = 1 :=
        hg.submatrix_eq_one _ (skipRight_injective hi)
          (fun y e => by have := congrArg Fin.val e; simp [skipRight] at this; omega)
          (fun y e => by have := congrArg Fin.val e; simp [skipRight] at this; omega)
      rw [hR]
      refine submatrix_skipEquiv_of_left hi _ fun y c hyc => hg.apply_of_not_mem ?_
      rintro ⟨hy, hc⟩
      apply hyc
      constructor
      · rcases hy with hy | hy <;> rw [hy] <;> simp <;> omega
      · rcases hc with hc | hc <;> rw [hc] <;> simp <;> omega
    · have hge : i + 2 ≤ (j : ℕ) := by omega
      have hL : (F x).submatrix (skipLeft hi) (skipLeft hi) = 1 :=
        hg.submatrix_eq_one _ (skipLeft_injective hi)
          (fun y e => by
            have := congrArg Fin.val e; have := y.2; simp [skipLeft] at *; omega)
          (fun y e => by
            have := congrArg Fin.val e; have := y.2; simp [skipLeft] at *; omega)
      rw [hL]
      refine submatrix_skipEquiv_of_right hi _ fun y c hyc => hg.apply_of_not_mem ?_
      rintro ⟨hy, hc⟩
      apply hyc
      constructor
      · rcases hy with hy | hy <;> rw [hy] <;> simp <;> omega
      · rcases hc with hc | hc <;> rw [hc] <;> simp <;> omega

theorem IsChainListSkip.isChainList_left (h : IsChainListSkip i l F E a b) :
    IsChainList l (fun x => (F x).submatrix (skipLeft hi) (skipLeft hi))
      (fun x => leftEdge (E x)) (fun j => a ⟨j, by omega⟩) (fun j => b ⟨j, by omega⟩) where
  eq_one x hx hE := by
    cases hEx : E x with
    | none => simp only [h.eq_one x hx hEx]; exact submatrix_one _ (skipLeft_injective hi)
    | some j =>
      have hj := h.edge_ne hx hEx
      have hlt : ¬(j : ℕ) < i := by
        intro hlt; rw [hEx] at hE; simp [leftEdge, hlt] at hE
      exact (h.isChainFactor x hx j hEx).submatrix_eq_one _ (skipLeft_injective hi)
        (fun y e => by have := congrArg Fin.val e; have := y.2; simp [skipLeft] at *; omega)
        (fun y e => by have := congrArg Fin.val e; have := y.2; simp [skipLeft] at *; omega)
  isChainFactor x hx j hE := by
    have hE' := (leftEdge_eq_some hi).mp hE
    exact (h.isChainFactor x hx _ hE').submatrix_of_embedding _ (skipLeft_injective hi) j
      (Fin.ext (by simp [skipLeft])) (Fin.ext (by simp [skipLeft]))
  countP_eq_one j := by
    rw [List.countP_congr (q := fun x => decide (E x = some ⟨j, by omega⟩))
      (fun x _ => by simp [leftEdge_eq_some hi])]
    exact h.countP_eq_one _ (by simp; omega) (by simp; omega)

theorem IsChainListSkip.isChainList_right (h : IsChainListSkip i l F E a b) :
    IsChainList l (fun x => (F x).submatrix (skipRight hi) (skipRight hi))
      (fun x => rightEdge hi (E x)) (fun j => a ⟨i + 2 + j, by omega⟩)
      (fun j => b ⟨i + 2 + j, by omega⟩) where
  eq_one x hx hE := by
    cases hEx : E x with
    | none => simp only [h.eq_one x hx hEx]; exact submatrix_one _ (skipRight_injective hi)
    | some j =>
      have hj := h.edge_ne hx hEx
      have hlt : ¬i + 2 ≤ (j : ℕ) := by
        intro hge; rw [hEx] at hE; simp [rightEdge, hge] at hE
      exact (h.isChainFactor x hx j hEx).submatrix_eq_one _ (skipRight_injective hi)
        (fun y e => by have := congrArg Fin.val e; simp [skipRight] at this; omega)
        (fun y e => by have := congrArg Fin.val e; simp [skipRight] at this; omega)
  isChainFactor x hx j hE := by
    have hE' := (rightEdge_eq_some hi).mp hE
    exact (h.isChainFactor x hx _ hE').submatrix_of_embedding _ (skipRight_injective hi) j
      (Fin.ext (by simp [skipRight])) (Fin.ext (by simp [skipRight]; omega))
  countP_eq_one j := by
    rw [List.countP_congr (q := fun x => decide (E x = some ⟨i + 2 + j, by omega⟩))
      (fun x _ => by simp [rightEdge_eq_some hi])]
    exact h.countP_eq_one _ (by simp; omega) (by simp; omega)

end Lists

theorem submatrix_one_add_smul_single {V W : Type*} [DecidableEq V] [DecidableEq W] (e : V ≃ W)
    (c : R) (m r : W) :
    (1 + c • single m r (1 : R)).submatrix e e = 1 + c • single (e.symm m) (e.symm r) 1 := by
  rw [show (1 + c • single m r (1 : R)).submatrix e e =
      (1 : Matrix W W R).submatrix e e + c • (single m r (1 : R)).submatrix e e from rfl,
    submatrix_one_equiv, submatrix_single_equiv]

section Main

variable {L i : ℕ} (hi : i + 2 ≤ L)

/-- **The modified chain in path indexing.** On the chain `Fin (L + 1)`, let `R` be a product of
chain factors, in any order, with every edge other than `i` and `i + 1` occurring exactly once,
and let `g` be the skip factor across the middle vertex `i + 1`. Multiply on the left by
`(1 + cb E_{i+1, i+2}) (1 + ca E_{i, i+1})`. Then
`det (1 - U g R) = -(ca * cb * mu * ∏_{j < i} a_j * b_j)`, provided the scalars of the edges below
`i` are units. -/
theorem det_one_sub_skipChain {g : Matrix (Fin (L + 1)) (Fin (L + 1)) R} {lam mu : R}
    (hg : IsSkipFactor hi g lam mu) {ι : Type*} {l : List ι}
    {F : ι → Matrix (Fin (L + 1)) (Fin (L + 1)) R} {E : ι → Option (Fin L)} {a b : Fin L → R}
    (hl : IsChainListSkip i l F E a b) (ha : ∀ j : Fin L, (j : ℕ) < i → IsUnit (a j))
    (hb : ∀ j : Fin L, (j : ℕ) < i → IsUnit (b j)) (ca cb : R) :
    (1 - (1 + cb • single (⟨i + 1, by omega⟩ : Fin (L + 1))
          (⟨i + 2, by omega⟩ : Fin (L + 1)) (1 : R)) *
        (1 + ca • single (⟨i, by omega⟩ : Fin (L + 1)) (⟨i + 1, by omega⟩ : Fin (L + 1)) (1 : R)) *
          (g * (l.map F).prod)).det =
      -(ca * cb * mu * ∏ j : Fin i, a ⟨j, by omega⟩ * b ⟨j, by omega⟩) := by
  have hm : (skipEquiv hi).symm ⟨i + 1, by omega⟩ = Sum.inr () := by
    rw [Equiv.symm_apply_eq]; exact Fin.ext (by simp)
  have hr : (skipEquiv hi).symm ⟨i + 2, by omega⟩ = Sum.inl (Sum.inr 0) := by
    rw [Equiv.symm_apply_eq]; exact Fin.ext (by simp)
  have hlt : (skipEquiv hi).symm ⟨i, by omega⟩ = Sum.inl (Sum.inl (Fin.last i)) := by
    rw [Equiv.symm_apply_eq]; exact Fin.ext (by simp)
  rw [← det_submatrix_equiv_self (skipEquiv hi), submatrix_one_sub _ (skipEquiv hi).injective,
    ← submatrix_mul_equiv (e₂ := skipEquiv hi), ← submatrix_mul_equiv (e₂ := skipEquiv hi),
    ← submatrix_mul_equiv (e₂ := skipEquiv hi), hg.submatrix_skipEquiv hi,
    submatrix_skipEquiv_prod hi l F _ _ (fun x hx => hl.submatrix_skipEquiv hi hx),
    submatrix_one_add_smul_single, submatrix_one_add_smul_single, hm, hr, hlt]
  have hblock :
      fromBlocks (g.submatrix (skipOuter hi) (skipOuter hi)) 0 0 (1 : Matrix Unit Unit R) *
      fromBlocks (fromBlocks (l.map fun x => (F x).submatrix (skipLeft hi) (skipLeft hi)).prod 0 0
        (l.map fun x => (F x).submatrix (skipRight hi) (skipRight hi)).prod) 0 0 1 =
      fromBlocks (g.submatrix (skipOuter hi) (skipOuter hi) *
        fromBlocks (l.map fun x => (F x).submatrix (skipLeft hi) (skipLeft hi)).prod 0 0
          (l.map fun x => (F x).submatrix (skipRight hi) (skipRight hi)).prod) 0 0 1 := by
    simp [fromBlocks_multiply]
  rw [hblock]
  exact det_one_sub_unipotent_mul_mergedChain (hg.isMergedFactor hi) (hl.isChainList_left hi)
    (fun j => ha _ (by simp)) (fun j => hb _ (by simp)) (hl.isChainList_right hi) ca cb

end Main

section Change

variable {d V : Type*} [Fintype d] [Fintype V] [DecidableEq d] [DecidableEq V]
  {P : Matrix d V R} {Q : Matrix V d R}

/-- `det (1 - M)` is unchanged by a change of basis given by mutually inverse rectangular
matrices. -/
theorem det_one_sub_conj (hPQ : P * Q = 1) (hQP : Q * P = 1) (M : Matrix d d R) :
    (1 - M).det = (1 - Q * M * P).det := by
  have hM : M = P * ((Q * M * P) * Q) := by
    simp only [← Matrix.mul_assoc, hPQ, Matrix.one_mul]
    rw [Matrix.mul_assoc, hPQ, Matrix.mul_one]
  conv_lhs => rw [hM]
  rw [det_one_sub_mul_comm, Matrix.mul_assoc, hQP, Matrix.mul_one]

omit [DecidableEq V] in
/-- The change of basis is multiplicative. -/
theorem conj_mul (hPQ : P * Q = 1) (M N : Matrix d d R) :
    Q * (M * N) * P = (Q * M * P) * (Q * N * P) := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P Q, hPQ, Matrix.one_mul]

theorem conj_list_prod (hPQ : P * Q = 1) (hQP : Q * P = 1) (l : List (Matrix d d R)) :
    Q * l.prod * P = (l.map fun M => Q * M * P).prod := by
  induction l with
  | nil => simpa using hQP
  | cons M l ih => rw [List.prod_cons, conj_mul hPQ, ih, List.map_cons, List.prod_cons]

omit [DecidableEq d] in
/-- If `M` sends the `c`-th column of `P` to `∑_w C w c • (column w of P)`, then the changed
matrix is `C`. -/
theorem conj_eq_of_mulVec (hQP : Q * P = 1) {M : Matrix d d R} {C : Matrix V V R}
    (h : ∀ c, M *ᵥ (fun r => P r c) = ∑ w, C w c • fun r => P r w) : Q * M * P = C := by
  have hMP : M * P = P * C := by
    ext r c
    have := congrFun (h c) r
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [mul_apply, mul_apply]
    rw [show (∑ j, M r j * P j c) = (M *ᵥ fun r => P r c) r from rfl, this]
    exact Finset.sum_congr rfl fun w _ => mul_comm _ _
  rw [Matrix.mul_assoc, hMP, ← Matrix.mul_assoc, hQP, Matrix.one_mul]

omit [DecidableEq d] in
/-- Column form: if `M` sends the `c`-th column of `P` to `∑_w coef w • (column w of P)`, then
column `c` of the changed matrix is `coef`. -/
theorem conj_apply_of_mulVec (hQP : Q * P = 1) {M : Matrix d d R} {c : V} {coef : V → R}
    (h : M *ᵥ (fun r => P r c) = ∑ w, coef w • fun r => P r w) (w : V) :
    (Q * M * P) w c = coef w := by
  have hcol : (Q * M * P) w c = (Q *ᵥ (M *ᵥ fun r => P r c)) w := by
    rw [Matrix.mul_assoc]; rfl
  rw [hcol, h, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hQPw : ∀ w', (Q *ᵥ fun r => P r w') w = (1 : Matrix V V R) w w' := by
    intro w'
    rw [← hQP]
    simp only [mulVec, dotProduct, mul_apply]
  simp only [hQPw, one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]

end Change

end Langlands.LinearAlgebra.ChainCoxeter
