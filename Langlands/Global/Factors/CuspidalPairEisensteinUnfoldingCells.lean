import Langlands.Global.Factors.CuspidalPairEisensteinRowEchelon
import Langlands.Global.Factors.CuspidalPairEisensteinOpenCell

/-! # Bruhat cells of the two-block parabolic relative to the upper unitriangular group

For the upper parabolic `P = blockShape r t` of `GL_N`, `N = r + t + 2`, with first block of size
`a = r + 1` and second block of size `b = t + 1`, this module chooses permutation representatives
`γ_J` of the double cosets `P(F) γ_J N₀(F)`, indexed by the subsets `J` of size `b`, with the
representative of the open cell `J₀ = {0, …, t}` equal to Shahidi's block Weyl element. For a
subset `J ≠ J₀` it produces a simple root `(k, k + 1)` with `k ∉ J` and `k + 1 ∈ J`, and shows that
conjugating the corresponding root element by any element of the pattern group `Λ_J` and then by
`γ_J` lands in the unipotent radical of `P`. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false

open Matrix

namespace Langlands.Global.CuspidalPairEisenstein

open RowEchelon

section BlockShape

variable {R : Type*} [CommRing R] {r t : ℕ}

theorem blockShape_index_val (i : Fin (blockShape r t).length) (x : Fin ((blockShape r t).size i)) :
    ((blockShape r t).index i x : ℕ) = (if (i : ℕ) = 0 then 0 else r + 1) + x := by
  change ((blockShape r t).indexEquiv ⟨i, x⟩).val = _
  rw [GeneralLinear.BlockShape.indexEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
    finSigmaFinEquiv_apply]
  rcases i with ⟨i, hi⟩
  change i < 2 at hi
  interval_cases i
  · simp
  · change (∑ k : Fin 1, ![r + 1, t + 1] (Fin.castLE (by omega : 1 ≤ 2) k)) + x.val = _
    rw [Fin.sum_univ_one]
    simp

theorem blockShape_size_val (i : Fin (blockShape r t).length) :
    (blockShape r t).size i = if (i : ℕ) = 0 then r + 1 else t + 1 := by
  rcases i with ⟨i, hi⟩
  change i < 2 at hi
  interval_cases i <;> rfl

/-- The two-block parabolic consists of the matrices with vanishing lower left block. -/
theorem mem_blockShape_parabolic_iff (g : Langlands.GeneralLinear (r + t + 2) R) :
    g ∈ (blockShape r t).parabolic R ↔
      ∀ i j : Fin (r + t + 2), r + 1 ≤ (i : ℕ) → (j : ℕ) < r + 1 → g i j = 0 := by
  rw [GeneralLinear.BlockShape.mem_parabolic_iff]
  constructor
  · intro h i j hi hj
    let i1 : Fin (blockShape r t).length := ⟨1, by change 1 < 2; omega⟩
    let i0 : Fin (blockShape r t).length := ⟨0, by change 0 < 2; omega⟩
    let x : Fin ((blockShape r t).size i1) := ⟨(i : ℕ) - (r + 1), by
      change _ < t + 1; omega⟩
    let y : Fin ((blockShape r t).size i0) := ⟨j, by change _ < r + 1; omega⟩
    have hb := h i1 i0 x y (by change (0 : ℕ) < 1; omega)
    have e1 : (blockShape r t).index i1 x = i := by
      apply Fin.ext
      rw [blockShape_index_val]
      change (if (1 : ℕ) = 0 then 0 else r + 1) + ((i : ℕ) - (r + 1)) = i
      simp only [one_ne_zero, ite_false]
      omega
    have e2 : (blockShape r t).index i0 y = j := by
      apply Fin.ext
      rw [blockShape_index_val]
      change (if (0 : ℕ) = 0 then 0 else r + 1) + (j : ℕ) = j
      simp
    rwa [e1, e2] at hb
  · intro h i j x y hji
    have hi : (i : ℕ) = 1 := by
      have := i.2
      change (i : ℕ) < 2 at this
      have : (j : ℕ) < i := hji
      omega
    have hj : (j : ℕ) = 0 := by
      have : (j : ℕ) < i := hji
      omega
    apply h
    · rw [blockShape_index_val, ite_eq_right (by omega)]
      omega
    · rw [blockShape_index_val, ite_eq_left hj]
      have hy := y.2
      have hs := blockShape_size_val (r := r) (t := t) j
      rw [ite_eq_left hj] at hs
      omega

/-- A matrix agreeing with the identity outside the upper right block lies in the unipotent
radical of the two-block parabolic. -/
theorem mem_blockShape_unipotentSubgroup_of (g : Langlands.GeneralLinear (r + t + 2) R)
    (h : ∀ i j : Fin (r + t + 2), ¬((i : ℕ) < r + 1 ∧ r + 1 ≤ (j : ℕ)) →
      (g : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) R) i j =
        (1 : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) R) i j) :
    g ∈ (blockShape r t).unipotentSubgroup R := by
  rw [GeneralLinear.BlockShape.mem_unipotentSubgroup_iff]
  refine ⟨(mem_blockShape_parabolic_iff g).mpr fun i j hi hj => ?_, fun i x y => ?_⟩
  · rw [h i j (by omega), Matrix.one_apply_ne]
    intro hij
    rw [hij] at hi
    omega
  · rw [h _ _ ?_]
    · by_cases hxy : x = y
      · subst hxy
        simp
      · rw [Matrix.one_apply_ne, ite_eq_right hxy]
        intro he
        exact hxy (((blockShape r t).index i).injective he)
    · rw [blockShape_index_val, blockShape_index_val]
      have hx := x.2
      have hy := y.2
      have hs := blockShape_size_val (r := r) (t := t) i
      split_ifs at hs ⊢ <;> omega

end BlockShape

section Permutation

variable {n : ℕ}

theorem card_subtype_le (a : ℕ) :
    Fintype.card {i : Fin n // a ≤ (i : ℕ)} = n - a := by
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun i : Fin n => a ≤ (i : ℕ)) =
      (Finset.univ.filter fun i : Fin n => (i : ℕ) < a)ᶜ := by
    ext i
    simp
  rw [this, Finset.card_compl, Fintype.card_fin, Fin.card_filter_val_lt, Nat.min_def]
  split_ifs <;> omega

/-- A permutation moving a subset `J` of size `n - a` onto the coordinates `≥ a`. -/
theorem exists_perm_mem_iff {a : ℕ} (J : Finset (Fin n)) (hJ : J.card = n - a) :
    ∃ σ : Equiv.Perm (Fin n), ∀ j, j ∈ J ↔ a ≤ (σ j : ℕ) := by
  classical
  have h1 : Fintype.card {j // j ∈ J} = Fintype.card {i : Fin n // a ≤ (i : ℕ)} := by
    rw [Fintype.card_coe, hJ, card_subtype_le]
  have h2 : Fintype.card {j // j ∉ J} = Fintype.card {i : Fin n // ¬a ≤ (i : ℕ)} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, Fintype.card_coe, hJ,
      card_subtype_le, Fintype.card_fin]
  let e1 := Fintype.equivOfCardEq h1
  let e2 := Fintype.equivOfCardEq h2
  refine ⟨Equiv.subtypeCongr e1 e2, fun j => ?_⟩
  by_cases hj : j ∈ J
  · have : Equiv.subtypeCongr e1 e2 j = e1 ⟨j, hj⟩ := by
      simp [Equiv.subtypeCongr, Equiv.sumCompl, hj]
    rw [this]
    exact iff_of_true hj (e1 ⟨j, hj⟩).2
  · have : Equiv.subtypeCongr e1 e2 j = e2 ⟨j, hj⟩ := by
      simp [Equiv.subtypeCongr, Equiv.sumCompl, hj]
    rw [this]
    exact iff_of_false hj (e2 ⟨j, hj⟩).2

variable {K : Type*} [Field K]

theorem lowerRowSpace_permutation {a : ℕ} (σ : Equiv.Perm (Fin n)) (J : Finset (Fin n))
    (hσ : ∀ j, j ∈ J ↔ a ≤ (σ j : ℕ)) :
    lowerRowSpace a (GeneralLinear.permutation n K σ : Matrix (Fin n) (Fin n) K) =
      coordSpace J := by
  rw [← span_single_eq_coordSpace, lowerRowSpace]
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_ofPred_eq, Finset.mem_coe]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨σ.symm i, (hσ _).mpr (by simpa using hi), ?_⟩
    ext j
    simp only [GeneralLinear.permutation_entry, Pi.single_apply]
    by_cases h : σ j = i
    · rw [ite_eq_left h, ite_eq_left (by rw [← h, Equiv.symm_apply_apply])]
    · rw [ite_eq_right h, ite_eq_right]
      rintro rfl
      exact h (Equiv.apply_symm_apply σ i)
  · rintro ⟨j, hj, rfl⟩
    refine ⟨σ j, (hσ j).mp hj, ?_⟩
    ext k
    simp only [GeneralLinear.permutation_entry, Pi.single_apply]
    by_cases h : k = j
    · subst h
      simp
    · rw [ite_eq_right h, ite_eq_right]
      exact fun h' => h (σ.injective h')

theorem reindex_permutation {m : ℕ} (R : Type*) [CommRing R] (e : Fin m ≃ Fin n)
    (π : Equiv.Perm (Fin m)) :
    GeneralLinear.reindex e (GeneralLinear.permutation m R π) =
      GeneralLinear.permutation n R (e.permCongr π) := by
  apply Units.ext
  ext i j
  change (GeneralLinear.permutation m R π : Matrix (Fin m) (Fin m) R) (e.symm i) (e.symm j) = _
  rw [GeneralLinear.permutation_entry, GeneralLinear.permutation_entry, Equiv.permCongr_apply]
  congr 1
  exact propext ⟨fun h => by rw [h, Equiv.apply_symm_apply], fun h => by
    rw [← h, Equiv.symm_apply_apply]⟩

end Permutation

section OpenCell

variable {r t : ℕ}

/-- The coordinates of the open cell: the first `t + 1` positions. -/
def openPivots (r t : ℕ) : Finset (Fin (r + t + 2)) :=
  Finset.univ.filter fun j => (j : ℕ) < t + 1

theorem card_openPivots : (openPivots r t).card = r + t + 2 - (r + 1) := by
  rw [openPivots, Fin.card_filter_val_lt, Nat.min_def]
  split_ifs <;> omega

theorem blockWeylPermutation_val (m n : ℕ) (x : Fin (m + n)) :
    (Shahidi.blockWeylPermutation m n x : ℕ) = if (x : ℕ) < n then m + x else x - n := by
  obtain ⟨v, hv⟩ := x
  by_cases h : v < n
  · simp [Shahidi.blockWeylPermutation, finAddFlip_apply_mk_left h, h]
  · simp only [Shahidi.blockWeylPermutation, Equiv.trans_apply, finCongr_apply, Fin.cast_mk]
    rw [finAddFlip_apply_mk_right (not_lt.mp h)]
    simp [h]

/-- The permutation of Shahidi's block Weyl element, reindexed to size `r + t + 2`. -/
def openCellPermutation (r t : ℕ) : Equiv.Perm (Fin (r + t + 2)) :=
  (finCongr (by omega : r + 1 + (t + 1) = r + t + 2)).permCongr
    (Shahidi.blockWeylPermutation (r + 1) (t + 1))

theorem openCellPermutation_val (j : Fin (r + t + 2)) :
    (openCellPermutation r t j : ℕ) =
      if (j : ℕ) < t + 1 then r + 1 + j else j - (t + 1) := by
  rw [openCellPermutation, Equiv.permCongr_apply, finCongr_apply, Fin.val_cast,
    blockWeylPermutation_val]
  simp

theorem mem_openPivots_iff (j : Fin (r + t + 2)) :
    j ∈ openPivots r t ↔ r + 1 ≤ (openCellPermutation r t j : ℕ) := by
  rw [openPivots, Finset.mem_filter, openCellPermutation_val]
  simp only [Finset.mem_univ, true_and]
  have := j.2
  split_ifs with h <;> omega

theorem openCellWeyl_eq_permutation (F : Type*) [Field F] [NumberField F] :
    openCellWeyl F r t = GeneralLinear.permutation (r + t + 2) (Adeles F) (openCellPermutation r t) := by
  rw [openCellWeyl, Shahidi.blockWeyl, reindex_permutation]
  rfl

theorem rational_permutation (F : Type*) [Field F] [NumberField F] {n : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    AdelicGL.rational F n (GeneralLinear.permutation n F σ) =
      GeneralLinear.permutation n (Adeles F) σ := by
  apply Units.ext
  ext i j
  rw [AdelicGL.rational_apply, GeneralLinear.permutation_entry, GeneralLinear.permutation_entry]
  split_ifs <;> simp

end OpenCell

section Representatives

variable (r t : ℕ)

open Classical in
/-- The permutations of the cell representatives: Shahidi's block Weyl permutation for the open
cell, and otherwise a chosen permutation moving `J` onto the coordinates `≥ r + 1`. -/
def cellPermutation (J : Finset (Fin (r + t + 2))) : Equiv.Perm (Fin (r + t + 2)) :=
  if J = openPivots r t then openCellPermutation r t
  else if h : J.card = r + t + 2 - (r + 1) then (exists_perm_mem_iff J h).choose else 1

theorem mem_iff_cellPermutation (J : Finset (Fin (r + t + 2)))
    (hJ : J.card = r + t + 2 - (r + 1)) (j : Fin (r + t + 2)) :
    j ∈ J ↔ r + 1 ≤ (cellPermutation r t J j : ℕ) := by
  unfold cellPermutation
  split_ifs with h0
  · subst h0
    exact mem_openPivots_iff j
  · exact (exists_perm_mem_iff J hJ).choose_spec j

theorem cellPermutation_openPivots :
    cellPermutation r t (openPivots r t) = openCellPermutation r t := by
  unfold cellPermutation
  rw [ite_eq_left rfl]

/-- The cell representative `γ_J`, a rational permutation matrix. -/
def cellRep (F : Type*) [Field F] (J : Finset (Fin (r + t + 2))) :
    Langlands.GeneralLinear (r + t + 2) F :=
  GeneralLinear.permutation (r + t + 2) F (cellPermutation r t J)

theorem lowerRowSpace_cellRep (F : Type*) [Field F] (J : Finset (Fin (r + t + 2)))
    (hJ : J.card = r + t + 2 - (r + 1)) :
    lowerRowSpace (r + 1) (cellRep r t F J : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) F) =
      coordSpace J :=
  lowerRowSpace_permutation _ J (mem_iff_cellPermutation r t J hJ)

theorem rational_cellRep_eq_permutation (F : Type*) [Field F] [NumberField F]
    (J : Finset (Fin (r + t + 2))) :
    AdelicGL.rational F (r + t + 2) (cellRep r t F J) =
      GeneralLinear.permutation (r + t + 2) (Adeles F) (cellPermutation r t J) :=
  rational_permutation F _

theorem rational_cellRep_openPivots (F : Type*) [Field F] [NumberField F] :
    AdelicGL.rational F (r + t + 2) (cellRep r t F (openPivots r t)) = openCellWeyl F r t := by
  rw [cellRep, rational_permutation, cellPermutation_openPivots, openCellWeyl_eq_permutation]

/-- **The orbit decomposition of `P(F) \ GL_N(F)` under `N₀(F)`.** -/
theorem cellOrbitMap_bijective (F : Type*) [Field F] :
    Function.Bijective (orbitMap (r + 1) ((blockShape r t).parabolic F) (cellRep r t F)) :=
  orbitMap_bijective (r + 1) _ (fun g => mem_blockShape_parabolic_iff g) _
    (lowerRowSpace_cellRep r t F)

end Representatives

section Singular

variable {r t : ℕ}

/-- A subset of size `t + 1` other than the open pivots contains `k + 1` but not `k` for some
`k`. -/
theorem exists_simpleRoot_of_ne_openPivots (J : Finset (Fin (r + t + 2)))
    (hJ : J.card = r + t + 2 - (r + 1)) (hne : J ≠ openPivots r t) :
    ∃ k k' : Fin (r + t + 2), (k' : ℕ) = k + 1 ∧ k ∉ J ∧ k' ∈ J := by
  by_contra hcon
  push Not at hcon
  apply hne
  have hdown : ∀ j : Fin (r + t + 2), j ∉ J → ∀ d : ℕ, ∀ i : Fin (r + t + 2),
      (i : ℕ) = j + d → i ∉ J := by
    intro j hj d
    induction d with
    | zero => intro i hi; rwa [show i = j from Fin.ext (by simpa using hi)]
    | succ d ih =>
      intro i hi
      have hi' : (j : ℕ) + d < r + t + 2 := by have := i.2; omega
      exact hcon ⟨j + d, hi'⟩ i (by simp; omega) (ih _ rfl)
  have hsub : openPivots r t ⊆ J := by
    intro j hj
    by_contra hjJ
    have hle : J ⊆ Finset.univ.filter fun i : Fin (r + t + 2) => (i : ℕ) < j := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra hij
      exact hdown j hjJ ((i : ℕ) - j) i (by omega) hi
    have hcard := Finset.card_le_card hle
    rw [Fin.card_filter_val_lt, hJ] at hcard
    simp only [openPivots, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have := Nat.min_le_right (r + t + 2) (j : ℕ)
    omega
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hJ, card_openPivots])).symm

end Singular

section RootElement

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The root element `1 + y E_(k,k')` as an invertible matrix. -/
def rootElement (k k' : Fin n) (hk : k ≠ k') (y : R) : Matrix.GeneralLinearGroup (Fin n) R where
  val := Matrix.transvection k k' y
  inv := Matrix.transvection k k' (-y)
  val_inv := by rw [Matrix.transvection_mul_transvection_same k k' hk, add_neg_cancel,
    Matrix.transvection_zero]
  inv_val := by rw [Matrix.transvection_mul_transvection_same k k' hk, neg_add_cancel,
    Matrix.transvection_zero]

theorem conj_rootElement_apply (k k' : Fin n) (hk : k ≠ k') (y : R)
    (g : Matrix.GeneralLinearGroup (Fin n) R) (p q : Fin n) :
    ((g * rootElement k k' hk y * g⁻¹ : Matrix.GeneralLinearGroup (Fin n) R) :
      Matrix (Fin n) (Fin n) R) p q =
      (1 : Matrix (Fin n) (Fin n) R) p q +
        (g : Matrix (Fin n) (Fin n) R) p k * y *
          ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) k' q := by
  rw [Units.val_mul, Units.val_mul]
  change ((g : Matrix (Fin n) (Fin n) R) * (1 + Matrix.single k k' y) *
    ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)) p q = _
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  rw [Finset.sum_eq_single k']
  · rw [Matrix.mul_single_apply_same]
  · intro l _ hl
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hl, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Conjugating a root element into the unipotent radical.** If `σ` moves `J` onto the
coordinates `≥ a`, `g ∈ Λ_J`, `k ∉ J` and `k' ∈ J`, then the conjugate of `g x g⁻¹`, with
`x = 1 + y E_(k,k')`, by the permutation matrix of `σ` agrees with the identity outside the
rows `< a` and columns `≥ a`. -/
theorem permutation_conj_rootElement_apply {a : ℕ} (σ : Equiv.Perm (Fin n))
    (J : Finset (Fin n)) (hσ : ∀ j, j ∈ J ↔ a ≤ (σ j : ℕ)) {g : Matrix.GeneralLinearGroup (Fin n) R}
    (hg : g ∈ stabilizer (R := R) J) {k k' : Fin n} (hk : k ≠ k') (hkJ : k ∉ J) (hk'J : k' ∈ J)
    (y : R) (i j : Fin n) (hij : ¬((i : ℕ) < a ∧ a ≤ (j : ℕ))) :
    ((GeneralLinear.permutation n R σ * (g * rootElement k k' hk y * g⁻¹) *
      (GeneralLinear.permutation n R σ)⁻¹ : Matrix.GeneralLinearGroup (Fin n) R) :
        Matrix (Fin n) (Fin n) R) i j = (1 : Matrix (Fin n) (Fin n) R) i j := by
  rw [GeneralLinear.permutation_conjugate_entry, conj_rootElement_apply]
  have hone : (1 : Matrix (Fin n) (Fin n) R) (σ⁻¹ i) (σ⁻¹ j) =
      (1 : Matrix (Fin n) (Fin n) R) i j := by
    by_cases h : i = j
    · subst h; simp
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne]
      exact fun h' => h (σ⁻¹.injective h')
  rw [hone]
  have hginv : g⁻¹ ∈ stabilizer (R := R) J := (stabilizer J).inv_mem hg
  have hσi : σ⁻¹ i ∈ J ↔ a ≤ (i : ℕ) := by rw [hσ]; simp
  have hσj : σ⁻¹ j ∈ J ↔ a ≤ (j : ℕ) := by rw [hσ]; simp
  by_cases hi : a ≤ (i : ℕ)
  · rw [hg.2 _ (hσi.mpr hi) k hkJ]
    simp
  · have hj : ¬a ≤ (j : ℕ) := fun hj => hij ⟨by omega, hj⟩
    rw [hginv.2 k' hk'J _ (fun h => hj (hσj.mp h))]
    simp

/-- The root element `1 + y E_(k,k')` with `k < k'` is upper unitriangular. -/
theorem rootElement_mem_upperUnipotent {k k' : Fin n} (hk : k < k') (y : R) :
    rootElement k k' hk.ne y ∈ GeneralLinear.upperUnipotent n R := by
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · change (1 + Matrix.single k k' y : Matrix (Fin n) (Fin n) R) i j = 0
    have hji' : j < i := hji
    rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_lt hji').symm, zero_add,
      Matrix.single_apply_of_ne]
    rintro ⟨rfl, rfl⟩
    exact lt_asymm hk hji'
  · change (1 + Matrix.single k k' y : Matrix (Fin n) (Fin n) R) i i = 1
    rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply_of_ne, add_zero]
    rintro ⟨rfl, h⟩
    exact hk.ne h.symm

/-- The root element lies in the pattern group of `J` when `k ∉ J`. -/
theorem rootElement_mem_stabilizer {J : Finset (Fin n)} {k k' : Fin n} (hk : k < k') (hkJ : k ∉ J)
    (y : R) : rootElement k k' hk.ne y ∈ stabilizer (R := R) J := by
  refine ⟨rootElement_mem_upperUnipotent hk y, fun i hi j hj => ?_⟩
  change (1 + Matrix.single k k' y : Matrix (Fin n) (Fin n) R) i j = 0
  rw [Matrix.add_apply, Matrix.one_apply_ne, zero_add, Matrix.single_apply_of_ne]
  · rintro ⟨rfl, -⟩
    exact hkJ hi
  · rintro rfl
    exact hj hi

/-- The superdiagonal entries of a simple root element sum to its coefficient. -/
theorem sum_superdiag_rootElement {m : ℕ} {k k' : Fin (m + 1)} (hkk' : (k' : ℕ) = k + 1) (y : R) :
    ∑ i : Fin m, (rootElement k k' (fun h => by rw [h] at hkk'; omega) y :
      Matrix (Fin (m + 1)) (Fin (m + 1)) R) i.castSucc i.succ = y := by
  have hk : (k : ℕ) < m := by have := k'.2; omega
  change ∑ i : Fin m, (1 + Matrix.single k k' y : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    i.castSucc i.succ = y
  rw [Finset.sum_eq_single ⟨k, hk⟩]
  · rw [Matrix.add_apply, Matrix.one_apply_ne (Fin.castSucc_lt_succ).ne]
    have h1 : (⟨k, hk⟩ : Fin m).castSucc = k := Fin.ext rfl
    have h2 : (⟨k, hk⟩ : Fin m).succ = k' := Fin.ext (by simp [hkk'])
    rw [h1, h2, Matrix.single_apply_same, zero_add]
  · intro i _ hi
    rw [Matrix.add_apply, Matrix.one_apply_ne (Fin.castSucc_lt_succ).ne, zero_add,
      Matrix.single_apply_of_ne]
    rintro ⟨h, -⟩
    exact hi (Fin.ext (by have := congrArg Fin.val h; simpa using this.symm))
  · intro h
    exact absurd (Finset.mem_univ _) h

end RootElement

section ParabolicConj

variable {R : Type*} [CommRing R] {r t : ℕ}

/-- Conjugating the pattern group of `J` by the cell representative lands in the parabolic. -/
theorem permutation_conj_mem_parabolic (σ : Equiv.Perm (Fin (r + t + 2)))
    (J : Finset (Fin (r + t + 2))) (hσ : ∀ j, j ∈ J ↔ r + 1 ≤ (σ j : ℕ))
    {g : Matrix.GeneralLinearGroup (Fin (r + t + 2)) R} (hg : g ∈ stabilizer (R := R) J) :
    GeneralLinear.permutation (r + t + 2) R σ * g * (GeneralLinear.permutation (r + t + 2) R σ)⁻¹ ∈
      (blockShape r t).parabolic R := by
  rw [mem_blockShape_parabolic_iff]
  intro i j hi hj
  rw [GeneralLinear.permutation_conjugate_entry]
  apply hg.2
  · rw [hσ]; simpa using hi
  · rw [hσ]; simpa using hj

/-- The conjugate of the root element by an element of the pattern group and then by the cell
representative lies in the unipotent radical of the parabolic. -/
theorem permutation_conj_rootElement_mem (σ : Equiv.Perm (Fin (r + t + 2)))
    (J : Finset (Fin (r + t + 2))) (hσ : ∀ j, j ∈ J ↔ r + 1 ≤ (σ j : ℕ))
    {g : Matrix.GeneralLinearGroup (Fin (r + t + 2)) R} (hg : g ∈ stabilizer (R := R) J)
    {k k' : Fin (r + t + 2)} (hk : k ≠ k') (hkJ : k ∉ J) (hk'J : k' ∈ J) (y : R) :
    GeneralLinear.permutation (r + t + 2) R σ * (g * rootElement k k' hk y * g⁻¹) *
      (GeneralLinear.permutation (r + t + 2) R σ)⁻¹ ∈ (blockShape r t).unipotentSubgroup R :=
  mem_blockShape_unipotentSubgroup_of _ fun i j hij =>
    permutation_conj_rootElement_apply σ J hσ hg hk hkJ hk'J y i j hij

end ParabolicConj

end Langlands.Global.CuspidalPairEisenstein
