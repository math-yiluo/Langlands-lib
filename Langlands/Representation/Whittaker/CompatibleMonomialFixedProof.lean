import Langlands.Representation.Whittaker.CompatibleMonomialFixedStatement
import Langlands.Representation.Whittaker.CompatibleTorus
import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations

/-!
# Compatible monomial representatives are fixed by Weyl-conjugated transpose

Proof of `CompatibleMonomialFixedStatement`. Testing compatibility on single root
elements shows that every ascent of the permutation is a step by one carrying equal
diagonal entries, and that consecutive values are taken at consecutive places when
taken in increasing order. A block induction then shows that the permutation reverses
the order of consecutive blocks, keeps the order inside each block, and that the
diagonal parameter is constant on each block. This is the fixedness under
`weylTransposeHomeomorph`.
-/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear HarmonicAnalysis
open scoped BigOperators

universe uF

/-! ## Combinatorics of permutations without upward jumps -/

/-- A function that never jumps up by more than one between consecutive places
grows at most linearly. -/
private theorem le_add_of_step {m : ℕ} (f : ℕ → ℕ)
    (hstep : ∀ l, l + 1 < m → f (l + 1) ≤ f l + 1) {i j : ℕ} (hij : i ≤ j) (hj : j < m) :
    f j ≤ f i + (j - i) := by
  induction j, hij using Nat.le_induction with
  | base => omega
  | succ j hij ih =>
    have h1 := hstep j hj
    have h2 := ih (by omega)
    omega

/-- One block of the induction: if `[0, a)` is carried onto the top `a` values, the
place `k` of the next value `m - 1 - a` ends a block `[a, k]` on which `f` increases
by one at each step, and `[0, k + 1)` is carried onto the top `k + 1` values. -/
private theorem block_step {m : ℕ} (f g : ℕ → ℕ) (hg : ∀ c, c < m → g c < m)
    (hgf : ∀ i, i < m → g (f i) = i) (hfg : ∀ c, c < m → f (g c) = c)
    (hstep_f : ∀ l, l + 1 < m → f (l + 1) ≤ f l + 1)
    (hstep_g : ∀ c, c + 1 < m → g (c + 1) ≤ g c + 1)
    {a : ℕ} (ha : a < m) (hQ : ∀ i, i < m → (i < a ↔ m - a ≤ f i)) :
    ∃ k, a ≤ k ∧ k < m ∧ (∀ i, a ≤ i → i ≤ k → f i + k = m - 1 - a + i) ∧
      ∀ i, i < m → (i < k + 1 ↔ m - (k + 1) ≤ f i) := by
  have hcm : m - 1 - a < m := by omega
  have hkm := hg _ hcm
  have hfk := hfg _ hcm
  have hak : a ≤ g (m - 1 - a) := by
    by_contra h
    have h' := (hQ _ hkm).mp (by omega)
    omega
  have hlow : ∀ i, i < m → a ≤ i → f i < m - a := by
    intro i him hai
    by_contra h
    have h' := (hQ i him).mpr (by omega)
    omega
  have hblock : ∀ i, a ≤ i → i ≤ g (m - 1 - a) → f i + g (m - 1 - a) = m - 1 - a + i := by
    intro i hai hik
    have him : i < m := lt_of_le_of_lt hik hkm
    have h1 := le_add_of_step f hstep_f hik hkm
    have hfi := hlow i him hai
    have h2 := le_add_of_step g hstep_g (show f i ≤ m - 1 - a by omega) hcm
    rw [hgf i him] at h2
    omega
  refine ⟨g (m - 1 - a), hak, hkm, hblock, ?_⟩
  intro i him
  constructor
  · intro hik
    by_cases hia : i < a
    · have := (hQ i him).mp hia
      omega
    · have := hblock i (by omega) (by omega)
      omega
  · intro hfi
    by_contra hik
    have hfi' := hlow i him (by omega)
    have hblock' := hblock (f i + g (m - 1 - a) + a + 1 - m) (by omega) (by omega)
    have heq : f (f i + g (m - 1 - a) + a + 1 - m) = f i := by omega
    have := congrArg g heq
    rw [hgf _ (by omega), hgf i him] at this
    omega

/-- If neither `f` nor its inverse `g` on `[0, m)` jumps up by more than one, then
`f (m - 1 - f j) = m - 1 - j`; if moreover `D` is unchanged across each step where
`f` increases by one, then `D (m - 1 - f j) = D j`. -/
private theorem block_reversal {α : Type*} {m : ℕ} (f g : ℕ → ℕ) (D : ℕ → α)
    (hf : ∀ i, i < m → f i < m) (hg : ∀ c, c < m → g c < m)
    (hgf : ∀ i, i < m → g (f i) = i) (hfg : ∀ c, c < m → f (g c) = c)
    (hstep_f : ∀ l, l + 1 < m → f (l + 1) ≤ f l + 1)
    (hstep_g : ∀ c, c + 1 < m → g (c + 1) ≤ g c + 1)
    (hD : ∀ l, l + 1 < m → f (l + 1) = f l + 1 → D (l + 1) = D l) :
    ∀ j, j < m → f (m - 1 - f j) = m - 1 - j ∧ D (m - 1 - f j) = D j := by
  have main : ∀ N a, m - a ≤ N → (∀ i, i < m → (i < a ↔ m - a ≤ f i)) →
      ∀ j, a ≤ j → j < m → f (m - 1 - f j) = m - 1 - j ∧ D (m - 1 - f j) = D j := by
    intro N
    induction N with
    | zero =>
      intro a hN _ j haj hj
      omega
    | succ N ih =>
      intro a hN hQ j haj hj
      obtain ⟨k, hak, hkm, hblock, hQ'⟩ :=
        block_step f g hg hgf hfg hstep_f hstep_g (show a < m by omega) hQ
      by_cases hjk : j ≤ k
      · have hfj := hblock j haj hjk
        have hj' : m - 1 - f j = a + k - j := by omega
        have hfj' := hblock (a + k - j) (by omega) (by omega)
        have hconst : ∀ i, a ≤ i → i ≤ k → D i = D a := by
          intro i hai hik
          induction i, hai using Nat.le_induction with
          | base => rfl
          | succ i hai ih2 =>
            have e1 := hblock i hai (by omega)
            have e2 := hblock (i + 1) (by omega) hik
            rw [hD i (by omega) (by omega), ih2 (by omega)]
        rw [hj']
        exact ⟨by omega, (hconst _ (by omega) (by omega)).trans (hconst j haj hjk).symm⟩
      · exact ih (k + 1) (by omega) hQ' j (by omega) hj
  exact fun j hj => main m 0 (by omega) (fun i hi => by have := hf i hi; omega) j
    (Nat.zero_le j) hj

/-! ## Root elements and their monomial conjugates -/

section Field

variable {F : Type uF} [Field F]

/-- The root element `1 + t E_{a b}` for `a < b`, as an upper-unipotent matrix. -/
private def rootElement {m : ℕ} {a b : Fin m} (hab : a < b) (t : F) :
    upperUnipotent m F :=
  ⟨Matrix.GeneralLinearGroup.transvection a b (ne_of_lt hab) t, by
    rw [mem_upperUnipotent_iff]
    constructor
    · intro i j hji
      change Matrix.transvection a b t i j = 0
      have hroot : ¬ (a = i ∧ b = j) := by
        rintro ⟨rfl, rfl⟩
        exact (lt_asymm hab) hji
      simp [Matrix.transvection, (ne_of_gt hji), hroot]
    · intro i
      change Matrix.transvection a b t i i = 1
      have hroot : ¬ (a = i ∧ b = i) := by
        rintro ⟨rfl, h⟩
        exact (ne_of_lt hab) h.symm
      simp [Matrix.transvection, hroot]⟩

private theorem rootElement_entry {m : ℕ} {a b : Fin m} (hab : a < b) (t : F)
    (i j : Fin m) :
    (rootElement hab t).val i j =
      (if i = j then 1 else 0) + (if a = i ∧ b = j then t else 0) := by
  change Matrix.transvection a b t i j = _
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]

/-- A first-superdiagonal sum with a single possible entry, at `(x, y)`. -/
private theorem superdiagonal_sum_single {n : ℕ} (x y : Fin (n + 1)) (c : F) :
    (∑ l : Fin n, if x = l.castSucc ∧ y = l.succ then c else 0) =
      if x.val + 1 = y.val then c else 0 := by
  classical
  split_ifs with h
  · have hx : x.val < n := by omega
    rw [Finset.sum_eq_single ⟨x.val, hx⟩]
    · rw [ite_eq_left]
      constructor
      · ext
        simp
      · ext
        simp [h]
    · intro l _ hl
      rw [ite_eq_right]
      rintro ⟨h1, _⟩
      apply hl
      ext
      simp [h1]
    · simp
  · apply Finset.sum_eq_zero
    intro l _
    rw [ite_eq_right]
    rintro ⟨rfl, rfl⟩
    simp at h

/-- The superdiagonal sum of a root element. -/
private theorem rootElement_sum {n : ℕ} {a b : Fin (n + 1)} (hab : a < b) (t : F) :
    (∑ l : Fin n, (rootElement hab t).val l.castSucc l.succ) =
      if a.val + 1 = b.val then t else 0 := by
  rw [← superdiagonal_sum_single]
  apply Finset.sum_congr rfl
  intro l _
  rw [rootElement_entry, ite_eq_right (ne_of_lt l.castSucc_lt_succ), zero_add]

/-- The superdiagonal sum of the monomial conjugate of a root element. -/
private theorem rootElement_conjugate_sum {n : ℕ} (w : Equiv.Perm (Fin (n + 1)))
    (d : Fin (n + 1) → Fˣ) {a b : Fin (n + 1)} (hab : a < b) (t : F) :
    (∑ l : Fin n, (permutation (n + 1) F w * Iwasawa.diagonalUnits d *
        (rootElement hab t).val * (permutation (n + 1) F w * Iwasawa.diagonalUnits d)⁻¹)
          l.castSucc l.succ) =
      if (w a).val + 1 = (w b).val then (d a : F) * t * (d b : F)⁻¹ else 0 := by
  rw [← superdiagonal_sum_single]
  apply Finset.sum_congr rfl
  intro l _
  rw [monomial_conjugate_entry, rootElement_entry]
  have hne : w⁻¹ l.castSucc ≠ w⁻¹ l.succ := fun h =>
    (ne_of_lt l.castSucc_lt_succ) (w⁻¹.injective h)
  rw [ite_eq_right hne, zero_add]
  by_cases h : w a = l.castSucc ∧ w b = l.succ
  · obtain ⟨h1, h2⟩ := h
    have e1 : w⁻¹ l.castSucc = a := Equiv.Perm.inv_eq_iff_eq.mpr h1.symm
    have e2 : w⁻¹ l.succ = b := Equiv.Perm.inv_eq_iff_eq.mpr h2.symm
    rw [e1, e2, ite_eq_left ⟨rfl, rfl⟩, ite_eq_left ⟨h1, h2⟩]
  · rw [ite_eq_right h, ite_eq_right, mul_zero, zero_mul]
    rintro ⟨h1, h2⟩
    apply h
    exact ⟨Equiv.Perm.eq_inv_iff_eq.mp h1, Equiv.Perm.eq_inv_iff_eq.mp h2⟩

/-- When `w a < w b`, the monomial conjugate of a root element at `(a, b)` is upper
unipotent. -/
private theorem rootElement_conjugate_mem {n : ℕ} (w : Equiv.Perm (Fin (n + 1)))
    (d : Fin (n + 1) → Fˣ) {a b : Fin (n + 1)} (hab : a < b) (hw : w a < w b) (t : F) :
    permutation (n + 1) F w * Iwasawa.diagonalUnits d * (rootElement hab t).val *
        (permutation (n + 1) F w * Iwasawa.diagonalUnits d)⁻¹ ∈
      upperUnipotent (n + 1) F := by
  rw [mem_upperUnipotent_iff]
  constructor
  · intro i j hji
    rw [monomial_conjugate_entry, rootElement_entry]
    have hne : w⁻¹ i ≠ w⁻¹ j := fun h => (ne_of_gt hji) (w⁻¹.injective h)
    have hroot : ¬ (a = w⁻¹ i ∧ b = w⁻¹ j) := by
      rintro ⟨h1, h2⟩
      rw [Equiv.Perm.eq_inv_iff_eq.mp h1, Equiv.Perm.eq_inv_iff_eq.mp h2] at hw
      exact (lt_asymm hw) hji
    rw [ite_eq_right hne, ite_eq_right hroot, add_zero, mul_zero, zero_mul]
  · intro i
    rw [monomial_conjugate_entry, rootElement_entry, ite_eq_left rfl]
    have hroot : ¬ (a = w⁻¹ i ∧ b = w⁻¹ i) := by
      rintro ⟨h1, h2⟩
      exact (ne_of_lt hab) (h1.trans h2.symm)
    rw [ite_eq_right hroot, add_zero, mul_one, mul_inv_cancel₀ (Units.ne_zero _)]

/-- The entries of a monomial matrix. -/
private theorem monomial_entry {m : ℕ} (w : Equiv.Perm (Fin m)) (d : Fin m → Fˣ)
    (i j : Fin m) :
    (permutation m F w * Iwasawa.diagonalUnits d) i j = if w j = i then (d j : F) else 0 := by
  change ((permutation m F w).val * (Iwasawa.diagonalUnits d).val) i j = _
  rw [Iwasawa.diagonalUnits_val, Matrix.mul_diagonal]
  rw [permutation_entry]
  split_ifs <;> simp

variable [TopologicalSpace F]

/-- A nontrivial additive character separates the linear functionals `t ↦ c t`. -/
private theorem eq_of_character_mul_eq (ψ : UnitaryAdditiveCharacter F) {c₁ c₂ : F}
    (h : ∀ t : F, ψ.complex (c₁ * t) = ψ.complex (c₂ * t)) : c₁ = c₂ := by
  by_contra hne
  have hsub : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr hne
  apply ψ.nontrivial
  ext x
  have hx := h (x / (c₁ - c₂))
  have hsplit : c₁ * (x / (c₁ - c₂)) = c₂ * (x / (c₁ - c₂)) + x := by
    field_simp
    ring
  rw [hsplit, AddChar.map_add_eq_mul] at hx
  have hne0 : ψ.complex (c₂ * (x / (c₁ - c₂))) ≠ 0 := by
    intro h0
    have := ψ.norm_complex (c₂ * (x / (c₁ - c₂)))
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have hone : ψ.complex x = 1 := by
    have := hx
    nth_rewrite 2 [← mul_one (ψ.complex (c₂ * (x / (c₁ - c₂))))] at this
    exact mul_left_cancel₀ hne0 this
  rw [UnitaryAdditiveCharacter.complex_apply] at hone
  rw [AddChar.one_apply, hone, Circle.coe_one]

/-- Compatibility tested on the root element at `(a, b)` with `a < b` and `w a < w b`. -/
private theorem root_coefficient_eq (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
    (w : Equiv.Perm (Fin (n + 1))) (d : Fin (n + 1) → Fˣ)
    (hs : IsCharacterCompatibleRepresentative ψ n
      (permutation (n + 1) F w * Iwasawa.diagonalUnits d))
    {a b : Fin (n + 1)} (hab : a < b) (hw : w a < w b) :
    (if a.val + 1 = b.val then (1 : F) else 0) =
      if (w a).val + 1 = (w b).val then (d a : F) * (d b : F)⁻¹ else 0 := by
  apply eq_of_character_mul_eq ψ
  intro t
  have hc := hs (rootElement hab t)
    ⟨_, rootElement_conjugate_mem w d hab hw t⟩ rfl
  have hc' := congrArg (fun z : ℂˣ => (z : ℂ)) hc
  simp only [standardCharacter_apply] at hc'
  rw [rootElement_sum, rootElement_conjugate_sum] at hc'
  convert hc' using 2
  · split_ifs <;> ring
  · split_ifs <;> ring

variable [IsTopologicalRing F]

/-- Over any field, a character-compatible monomial matrix
`permutation (n + 1) F w * Iwasawa.diagonalUnits d` is fixed by the Weyl-conjugated
transpose. -/
theorem weylTransposeHomeomorph_monomial_eq_of_compatible (ψ : UnitaryAdditiveCharacter F)
    {n : ℕ} (w : Equiv.Perm (Fin (n + 1))) (d : Fin (n + 1) → Fˣ)
    (hs : IsCharacterCompatibleRepresentative ψ n
      (permutation (n + 1) F w * Iwasawa.diagonalUnits d)) :
    weylTransposeHomeomorph n F (permutation (n + 1) F w * Iwasawa.diagonalUnits d) =
      permutation (n + 1) F w * Iwasawa.diagonalUnits d := by
  -- An ascent at consecutive places is a step by one with equal diagonal entries.
  have h1 : ∀ a b : Fin (n + 1), a.val + 1 = b.val → w a < w b →
      (w a).val + 1 = (w b).val ∧ d a = d b := by
    intro a b hab hw
    have hlt : a < b := by rw [Fin.lt_def]; omega
    have key := root_coefficient_eq ψ w d hs hlt hw
    rw [ite_eq_left hab] at key
    by_cases hc : (w a).val + 1 = (w b).val
    · rw [ite_eq_left hc] at key
      exact ⟨hc, Units.ext ((mul_inv_eq_one₀ (Units.ne_zero _)).mp key.symm)⟩
    · rw [ite_eq_right hc] at key
      exact absurd key one_ne_zero
  -- Consecutive values taken in increasing order are taken at consecutive places.
  have h2 : ∀ a b : Fin (n + 1), a < b → (w a).val + 1 = (w b).val → a.val + 1 = b.val := by
    intro a b hab hc
    have hw : w a < w b := by rw [Fin.lt_def]; omega
    have key := root_coefficient_eq ψ w d hs hab hw
    rw [ite_eq_left hc] at key
    by_contra h
    rw [ite_eq_right h] at key
    exact (mul_ne_zero (Units.ne_zero _) (inv_ne_zero (Units.ne_zero _))) key.symm
  -- Transfer to functions on natural numbers.
  let f : ℕ → ℕ := fun i => if h : i < n + 1 then (w ⟨i, h⟩).val else 0
  let g : ℕ → ℕ := fun c => if h : c < n + 1 then (w⁻¹ ⟨c, h⟩).val else 0
  let D : ℕ → Fˣ := fun i => if h : i < n + 1 then d ⟨i, h⟩ else 1
  have hf_val : ∀ i : Fin (n + 1), f i.val = (w i).val := fun i => by
    simp only [f]
    exact dite_eq_left i.isLt
  have hg_val : ∀ c : Fin (n + 1), g c.val = (w⁻¹ c).val := fun c => by
    simp only [g]
    exact dite_eq_left c.isLt
  have hD_val : ∀ i : Fin (n + 1), D i.val = d i := fun i => by
    simp only [D]
    exact dite_eq_left i.isLt
  have hf : ∀ i, i < n + 1 → f i < n + 1 := by
    intro i hi
    rw [show f i = _ from hf_val ⟨i, hi⟩]
    exact (w _).isLt
  have hg : ∀ c, c < n + 1 → g c < n + 1 := by
    intro c hc
    rw [show g c = _ from hg_val ⟨c, hc⟩]
    exact (w⁻¹ _).isLt
  have hgf : ∀ i, i < n + 1 → g (f i) = i := by
    intro i hi
    rw [show f i = _ from hf_val ⟨i, hi⟩, hg_val]
    simp
  have hfg : ∀ c, c < n + 1 → f (g c) = c := by
    intro c hc
    rw [show g c = _ from hg_val ⟨c, hc⟩, hf_val]
    simp
  have hstep_f : ∀ l, l + 1 < n + 1 → f (l + 1) ≤ f l + 1 := by
    intro l hl
    rw [show f (l + 1) = _ from hf_val ⟨l + 1, hl⟩,
      show f l = _ from hf_val ⟨l, by omega⟩]
    by_cases hw : w ⟨l, by omega⟩ < w ⟨l + 1, hl⟩
    · have := (h1 _ _ rfl hw).1
      omega
    · rw [not_lt, Fin.le_def] at hw
      omega
  have hstep_g : ∀ c, c + 1 < n + 1 → g (c + 1) ≤ g c + 1 := by
    intro c hc
    rw [show g (c + 1) = _ from hg_val ⟨c + 1, hc⟩,
      show g c = _ from hg_val ⟨c, by omega⟩]
    by_cases hab : w⁻¹ ⟨c, by omega⟩ < w⁻¹ ⟨c + 1, hc⟩
    · have := h2 _ _ hab (by simp)
      omega
    · rw [not_lt, Fin.le_def] at hab
      omega
  have hD : ∀ l, l + 1 < n + 1 → f (l + 1) = f l + 1 → D (l + 1) = D l := by
    intro l hl hfl
    rw [show f (l + 1) = _ from hf_val ⟨l + 1, hl⟩,
      show f l = _ from hf_val ⟨l, by omega⟩] at hfl
    rw [show D (l + 1) = _ from hD_val ⟨l + 1, hl⟩,
      show D l = _ from hD_val ⟨l, by omega⟩]
    have hw : w ⟨l, by omega⟩ < w ⟨l + 1, hl⟩ := by rw [Fin.lt_def]; omega
    exact (h1 _ _ rfl hw).2.symm
  have hrev := block_reversal f g D hf hg hgf hfg hstep_f hstep_g hD
  -- Back to `Fin (n + 1)`: `w` and `d` are compatible with reversal.
  have key : ∀ j : Fin (n + 1), w (w j).rev = j.rev ∧ d (w j).rev = d j := by
    intro j
    obtain ⟨e1, e2⟩ := hrev j.val j.isLt
    have hr : n + 1 - 1 - f j.val = ((w j).rev).val := by
      rw [hf_val, Fin.val_rev]
      omega
    rw [hr, hf_val] at e1
    rw [hr, hD_val, hD_val] at e2
    refine ⟨Fin.ext ?_, e2⟩
    rw [e1, Fin.val_rev]
    omega
  apply Units.ext
  ext i j
  rw [weylTransposeHomeomorph_entry, monomial_entry, monomial_entry]
  by_cases h : w j = i
  · subst h
    rw [ite_eq_left rfl, ite_eq_left (key j).1, (key j).2]
  · rw [ite_eq_right h, ite_eq_right]
    intro h'
    apply h
    have := (key i.rev).1
    rw [h', Fin.rev_rev, Fin.rev_rev] at this
    exact this

end Field

/-- Shalika's monomial fixed-point criterion (1.5) for canonical p-adic fields. -/
theorem compatibleMonomialFixed : CompatibleMonomialFixedStatement.{uF} := by
  intro p _ F n ψ w d s hs
  let := F.canonicalNormedField
  exact weylTransposeHomeomorph_monomial_eq_of_compatible ψ w d hs

end Langlands.Whittaker
