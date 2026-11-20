import Langlands.Representation.Archimedean.RealDiscreteShiftSort

/-!
# The source side of the separated discrete-series case

Let `cs` be a list of real characters (even ones first) and `Ds` a list of induction data of
nonzero weights, sorted by decreasing absolute weight, all with the same real exponent. The
source of the presentation is the principal series of
`x(D₁), …, x(D_d), cs, y(D_d), …, y(D₁)` (`srcChars`). This module chooses the bottom row sets
`R_j` (the `y`-rows of the blocks with `|m| ≥ j`, and for `j = 0` also the odd character rows),
shows that the source is the twist of an even list `ps''` by the minors with rows `R_j`
(`isMinorShift_src`), and computes `ps''` (`shiftList_eq_midList`).
-/

noncomputable section

open Finset

open scoped TensorProduct

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean Langlands.GeneralLinear

set_option autoImplicit false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealDiscreteSeparated

open RealDiscretePresentation RealDiscreteShift RealDiscreteSort RealDiscreteTightness
  RealTiedMinorProduct RealTiedMinorScalar RealDiscreteMinorCyclic RealInducedCharacter GramFormula

/-! ## Exponents of character lists -/

theorem realPositionExponent_map_character :
    ∀ (cs : List RealCharacterData) (i : ℕ) (hi : i < cs.length),
      realPositionExponent (cs.map RealBlock.character) i = cs[i].exponent
  | [], _, hi => by simp at hi
  | c :: cs, 0, _ => by simp [realPositionExponent]
  | c :: cs, i + 1, hi => by
      simp only [List.map_cons, realPositionExponent, List.getElem_cons_succ]
      exact realPositionExponent_map_character cs i (by simpa using hi)

/-! ## The source list -/

variable (cs : List RealCharacterData) (Ds : List ComplexCharacterData)

/-- The character `|·|^{t - ℓ/2}`. -/
def xChar (e : ComplexCharacterData) : RealCharacterData := cb e 0

/-- The character `sgn^{ℓ+1} |·|^{t + ℓ/2}`. -/
def yChar (e : ComplexCharacterData) : RealCharacterData := ca e (ySign e)

/-- The characters `x(D₁), …, x(D_d), cs, y(D_d), …, y(D₁)`. -/
def srcChars : List RealCharacterData := Ds.map xChar ++ cs ++ Ds.reverse.map yChar

theorem sourceList_eq :
    sourceList Ds (cs.map RealBlock.character) = (srcChars cs Ds).map RealBlock.character := by
  simp only [sourceList, srcChars, List.map_append, List.map_reverse, List.map_map]
  rfl

theorem srcChars_length :
    (srcChars cs Ds).length = Ds.length + cs.length + Ds.length := by
  simp only [srcChars, List.length_append, List.length_map, List.length_reverse]

theorem srcChars_x {i : ℕ} (hi : i < Ds.length) :
    (srcChars cs Ds)[i]'(by rw [srcChars_length]; omega) = xChar (Ds[i]) := by
  unfold srcChars
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
    List.getElem_map]

theorem srcChars_c {i : ℕ} (hi₁ : Ds.length ≤ i) (hi₂ : i < Ds.length + cs.length) :
    (srcChars cs Ds)[i]'(by rw [srcChars_length]; omega) = cs[i - Ds.length]'(by omega) := by
  unfold srcChars
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
  simp

theorem srcChars_y {i : ℕ} (hi₁ : Ds.length + cs.length ≤ i)
    (hi₂ : i < Ds.length + cs.length + Ds.length) :
    (srcChars cs Ds)[i]'(by rw [srcChars_length]; omega) =
      yChar (Ds.reverse[i - (Ds.length + cs.length)]'(by simp; omega)) := by
  unfold srcChars
  rw [List.getElem_append_right (by simp; omega)]
  simp

/-! ## Weights and parities by position -/

/-- `k_P = |m| + 1` for the `P`-th block of `Ds.reverse`, and `0` past the end. -/
def kOf (P : ℕ) : ℕ := (Ds.reverse.map fun e => e.weight.natAbs + 1).getD P 0

/-- The `x`-th character of `cs` is odd. -/
def oddAt (x : ℕ) : Prop := (cs.map fun c => c.parity.val).getD x 0 = 1

instance (x : ℕ) : Decidable (oddAt cs x) :=
  inferInstanceAs (Decidable (_ = 1))

theorem kOf_eq {P : ℕ} (hP : P < Ds.length) :
    kOf Ds P = (Ds.reverse[P]'(by simpa using hP)).weight.natAbs + 1 := by
  simp [kOf, List.getD_eq_getElem?_getD, hP]

theorem oddAt_iff {x : ℕ} (hx : x < cs.length) : oddAt cs x ↔ (cs[x]).parity.val = 1 := by
  simp [oddAt, List.getD_eq_getElem?_getD, hx]

theorem parity_val_of_not_oddAt {x : ℕ} (hx : x < cs.length) (h : ¬ oddAt cs x) :
    (cs[x]).parity.val = 0 := by
  rw [oddAt_iff cs hx] at h
  have := (cs[x]).parity.isLt
  omega

variable {cs Ds}

theorem kOf_mono (hsortD : Ds.Pairwise fun e f => f.weight.natAbs ≤ e.weight.natAbs)
    {P P' : ℕ} (hPP' : P ≤ P') (hP' : P' < Ds.length) : kOf Ds P ≤ kOf Ds P' := by
  rcases hPP'.lt_or_eq with h | h
  · rw [kOf_eq Ds (by omega), kOf_eq Ds hP']
    have hrev : Ds.reverse.Pairwise fun e f => e.weight.natAbs ≤ f.weight.natAbs :=
      List.pairwise_reverse.mpr hsortD
    have := List.pairwise_iff_getElem.mp hrev P P' (by simp; omega) (by simpa using hP') h
    omega
  · rw [h]

theorem kOf_pos {P : ℕ} (hP : P < Ds.length) : 1 ≤ kOf Ds P := by
  rw [kOf_eq Ds hP]
  omega

theorem kOf_le {N : ℕ} (hN : ∀ e ∈ Ds, e.weight.natAbs + 1 ≤ N) (P : ℕ) : kOf Ds P ≤ N := by
  by_cases hP : P < Ds.length
  · rw [kOf_eq Ds hP]
    exact hN _ (List.mem_reverse.mp (List.getElem_mem _))
  · have : kOf Ds P = 0 := by simp [kOf, List.getD_eq_getElem?_getD, not_lt.mp hP]
    omega

theorem oddAt_mono (hsortC : cs.Pairwise fun b c => b.parity.val ≤ c.parity.val)
    {x x' : ℕ} (hxx' : x ≤ x') (hx' : x' < cs.length) (h : oddAt cs x) : oddAt cs x' := by
  rcases hxx'.lt_or_eq with hlt | heq
  · rw [oddAt_iff cs (by omega)] at h
    rw [oddAt_iff cs hx']
    have h1 := List.pairwise_iff_getElem.mp hsortC x x' (by omega) hx' hlt
    have h2 := (cs[x']).parity.isLt
    omega
  · rw [← heq]
    exact h

/-! ## The row sets -/

variable (cs Ds)

/-- The row set `R_j`: the `y`-rows of the blocks with `k_P > j`, and for `j = 0` also the
rows of the odd characters. -/
def rowSet (n N : ℕ) (j : Fin N) : Finset (Fin n) :=
  univ.filter fun i : Fin n =>
    (Ds.length + cs.length ≤ (i : ℕ) ∧ (j : ℕ) < kOf Ds (i - (Ds.length + cs.length))) ∨
      ((j : ℕ) = 0 ∧ Ds.length ≤ (i : ℕ) ∧ (i : ℕ) < Ds.length + cs.length ∧
        oddAt cs (i - Ds.length))

/-- The number of row sets containing the row `i`. -/
def hitCount (i : ℕ) : ℕ :=
  if Ds.length + cs.length ≤ i then kOf Ds (i - (Ds.length + cs.length))
  else if Ds.length ≤ i ∧ oddAt cs (i - Ds.length) then 1 else 0

variable {cs Ds}

variable {n N : ℕ}

theorem isBottom_rowSet (hn : Ds.length + cs.length + Ds.length = n)
    (hsortD : Ds.Pairwise fun e f => f.weight.natAbs ≤ e.weight.natAbs)
    (hsortC : cs.Pairwise fun b c => b.parity.val ≤ c.parity.val)
    (j : Fin N) : IsBottom (rowSet cs Ds n N j) := by
  intro i i' hii' hi
  rw [Fin.le_def] at hii'
  have hi'n := i'.2
  simp only [rowSet, mem_filter, mem_univ, true_and] at hi ⊢
  rcases hi with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
  · left
    exact ⟨by omega, lt_of_lt_of_le h2 (kOf_mono hsortD (by omega) (by omega))⟩
  · by_cases hy : Ds.length + cs.length ≤ (i' : ℕ)
    · left
      exact ⟨hy, by rw [h1]; exact kOf_pos (by omega)⟩
    · right
      exact ⟨h1, by omega, by omega, oddAt_mono hsortC (by omega) (by omega) h4⟩

theorem colSet_rowSet (hN : ∀ e ∈ Ds, e.weight.natAbs + 1 ≤ N) (i : Fin n) :
    colSet (rowSet cs Ds n N) i = seg N (hitCount cs Ds i) := by
  have hk := kOf_le hN (i - (Ds.length + cs.length))
  ext j
  rw [mem_colSet, mem_seg]
  simp only [rowSet, mem_filter, mem_univ, true_and]
  unfold hitCount
  by_cases hy : Ds.length + cs.length ≤ (i : ℕ)
  · rw [ite_eq_left hy]
    constructor
    · rintro (⟨-, h⟩ | ⟨-, -, h, -⟩)
      · exact h
      · omega
    · intro h
      exact Or.inl ⟨hy, h⟩
  · rw [ite_eq_right hy]
    by_cases hx : Ds.length ≤ (i : ℕ) ∧ oddAt cs (i - Ds.length)
    · rw [ite_eq_left hx]
      constructor
      · rintro (⟨h, -⟩ | ⟨h, -⟩)
        · omega
        · omega
      · intro h
        exact Or.inr ⟨by omega, hx.1, by omega, hx.2⟩
    · rw [ite_eq_right hx]
      constructor
      · rintro (⟨h, -⟩ | ⟨-, h1, -, h2⟩)
        · omega
        · exact absurd ⟨h1, h2⟩ hx
      · intro h
        omega

theorem hits_rowSet (hN : ∀ e ∈ Ds, e.weight.natAbs + 1 ≤ N) (hN1 : 1 ≤ N) (i : Fin n) :
    hits (rowSet cs Ds n N) i = hitCount cs Ds i := by
  rw [hits, colSet_rowSet hN, card_seg]
  have hk := kOf_le hN (i - (Ds.length + cs.length))
  unfold hitCount
  split_ifs <;> omega

/-! ## The shift -/

theorem rowSet_parity (hn : Ds.length + cs.length + Ds.length = n)
    (hN : ∀ e ∈ Ds, e.weight.natAbs + 1 ≤ N) (hN1 : 1 ≤ N) (i : Fin n) :
    realPositionCharacter ((srcChars cs Ds).map RealBlock.character) i (-1) =
      (-1) ^ hits (rowSet cs Ds n N) i := by
  have hi : (i : ℕ) < (srcChars cs Ds).length := by rw [srcChars_length]; omega
  rw [RealTiedScalarAssembly.realPositionCharacter_map_character_neg_one _ _ hi,
    hits_rowSet hN hN1]
  unfold hitCount
  by_cases hy : Ds.length + cs.length ≤ (i : ℕ)
  · rw [ite_eq_left hy, srcChars_y cs Ds hy (by omega), kOf_eq Ds (by omega)]
    simp only [yChar, ca_parity, ySign]
    rw [neg_one_pow_eq_pow_mod_two (R := ℂ) (_ + 1)]
  · rw [ite_eq_right hy]
    by_cases hx : Ds.length ≤ (i : ℕ)
    · rw [srcChars_c cs Ds hx (by omega)]
      by_cases ho : oddAt cs (i - Ds.length)
      · rw [ite_eq_left ⟨hx, ho⟩, (oddAt_iff cs (by omega)).mp ho]
      · rw [ite_eq_right (fun h => ho h.2), parity_val_of_not_oddAt cs (by omega) ho]
    · rw [ite_eq_right (fun h => hx h.1), srcChars_x cs Ds (by omega)]
      simp [xChar]

/-- **The source is a shift.** -/
theorem isMinorShift_src (hn : Ds.length + cs.length + Ds.length = n)
    (hsortD : Ds.Pairwise fun e f => f.weight.natAbs ≤ e.weight.natAbs)
    (hsortC : cs.Pairwise fun b c => b.parity.val ≤ c.parity.val)
    (hN : ∀ e ∈ Ds, e.weight.natAbs + 1 ≤ N) (hN1 : 1 ≤ N) :
    IsMinorShift n ((shiftList n ((srcChars cs Ds).map RealBlock.character)
      (rowSet cs Ds n N)).map RealBlock.character)
      ((srcChars cs Ds).map RealBlock.character) (rowSet cs Ds n N) :=
  isMinorShift_shiftList (isPrincipal_map_character _)
    (isBottom_rowSet hn hsortD hsortC) (rowSet_parity hn hN hN1)

/-! ## The shifted list -/

variable (cs Ds)

/-- The shifted list `|·|^{t - ℓ/2}` (`x`-rows), `|·|^{t - ε}` (characters `sgn^ε |·|^t`),
`|·|^{t - ℓ/2 - 1}` (`y`-rows). -/
def midList : List RealCharacterData :=
  Ds.map (fun e => RealJacquetFrobenius.charData 0 (bExp e)) ++
    cs.map (fun c => RealJacquetFrobenius.charData 0 (c.exponent - (c.parity.val : ℂ))) ++
    Ds.reverse.map (fun e => RealJacquetFrobenius.charData 0
      (aExp e - ((e.weight.natAbs + 1 : ℕ) : ℂ)))

variable {cs Ds}

theorem midList_length : (midList cs Ds).length = Ds.length + cs.length + Ds.length := by
  simp only [midList, List.length_append, List.length_map, List.length_reverse]

theorem midList_x {i : ℕ} (hi : i < Ds.length) :
    (midList cs Ds)[i]'(by rw [midList_length]; omega) =
      RealJacquetFrobenius.charData 0 (bExp (Ds[i])) := by
  unfold midList
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
    List.getElem_map]

theorem midList_c {i : ℕ} (hi₁ : Ds.length ≤ i) (hi₂ : i < Ds.length + cs.length) :
    (midList cs Ds)[i]'(by rw [midList_length]; omega) =
      RealJacquetFrobenius.charData 0 ((cs[i - Ds.length]'(by omega)).exponent -
        ((cs[i - Ds.length]'(by omega)).parity.val : ℂ)) := by
  unfold midList
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
  simp

theorem midList_y {i : ℕ} (hi₁ : Ds.length + cs.length ≤ i)
    (hi₂ : i < Ds.length + cs.length + Ds.length) :
    (midList cs Ds)[i]'(by rw [midList_length]; omega) =
      RealJacquetFrobenius.charData 0
        (aExp (Ds.reverse[i - (Ds.length + cs.length)]'(by simp; omega)) -
          (((Ds.reverse[i - (Ds.length + cs.length)]'(by simp; omega)).weight.natAbs + 1 : ℕ) :
            ℂ)) := by
  unfold midList
  rw [List.getElem_append_right (by simp; omega)]
  simp

theorem shiftList_eq_midList (hn : Ds.length + cs.length + Ds.length = n)
    (hN : ∀ e ∈ Ds, e.weight.natAbs + 1 ≤ N) (hN1 : 1 ≤ N) :
    shiftList n ((srcChars cs Ds).map RealBlock.character) (rowSet cs Ds n N) =
      midList cs Ds := by
  apply List.ext_getElem
  · rw [shiftList_length, midList_length, hn]
  · intro i h₁ h₂
    have hi : i < n := by rwa [shiftList_length] at h₁
    simp only [shiftList, List.getElem_ofFn]
    rw [realPositionExponent_map_character _ _ (by rw [srcChars_length]; omega),
      hits_rowSet hN hN1 ⟨i, hi⟩]
    simp only [hitCount]
    by_cases hy : Ds.length + cs.length ≤ i
    · rw [ite_eq_left hy, srcChars_y cs Ds hy (by omega),
        midList_y hy (by omega), kOf_eq Ds (by omega)]
      rfl
    · rw [ite_eq_right hy]
      by_cases hx : Ds.length ≤ i
      · rw [srcChars_c cs Ds hx (by omega), midList_c hx (by omega)]
        by_cases ho : oddAt cs (i - Ds.length)
        · rw [ite_eq_left ⟨hx, ho⟩, (oddAt_iff cs (by omega)).mp ho]
        · rw [ite_eq_right (fun h => ho h.2), parity_val_of_not_oddAt cs (by omega) ho]
      · rw [ite_eq_right (fun h => hx h.1), srcChars_x cs Ds (by omega), midList_x (by omega)]
        simp [xChar]

end RealDiscreteSeparated

end Langlands.Archimedean
