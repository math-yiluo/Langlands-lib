import Langlands.Representation.Archimedean.ComplexParabolicChartBound
import Langlands.Representation.Archimedean.ComplexBlockChartIntegralStatement
import Langlands.Representation.Archimedean.ComplexBlockParabolicIntegrationStatement

/-!
# Growth of complex principal-series functions along the opposite unipotent radical of `P_{a,k}`

`ComplexBlockChart.norm_le_gram`: a function `F` of a principal series of `GL_{N+1}(ℂ)` bounded by
`C` on `U(N+1)` satisfies `‖F(y κ)‖ ≤ C ∏_{l ≥ 1} G_l(y)^{(σ_l − σ_{l−1})/2}` for every `y` with
`|det y| = 1`, where `G_l(y)` are the Gram determinants of the lower rows of `y`.
`ComplexBlockChart.gram_blockLower_le` and `gram_blockLower_ge` compute them for
`y = n̄(X) = [[1, 0], [X, 1]]`.
-/

noncomputable section

open MeasureTheory Matrix

open scoped Matrix

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace ComplexBlockChart

open ComplexMaximalParabolicIntegration ComplexParabolicChartBound Langlands.GeneralLinear

/-! ## The general growth bound -/

section General

variable {N : ℕ}

theorem prod_tail_sq_eq_gram (y κ : Langlands.GeneralLinear (N + 1) ℂ)
    (hκ : κ ∈ unitaryCompact ℂ (N + 1)) (a : Fin (N + 1) → ℂˣ) (u : upperUnipotent (N + 1) ℂ)
    (k : Langlands.GeneralLinear (N + 1) ℂ) (hk : k ∈ unitaryCompact ℂ (N + 1))
    (hg : y * κ = (Iwasawa.diagonalUnits a : Langlands.GeneralLinear (N + 1) ℂ) *
      (u : Langlands.GeneralLinear (N + 1) ℂ) * k) (l : ℕ) :
    ComplexGramFormula.gram l (y : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
        ((y : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ).map (starRingEnd ℂ)) =
      ((‖∏ j : Fin (N + 1), if l ≤ (j : ℕ) then (a j : ℂ) else 1‖ ^ 2 : ℝ) : ℂ) := by
  have hκ' := ComplexGramFormula.mul_conj_transpose_eq_one_of_mem hκ
  have hk' := ComplexGramFormula.mul_conj_transpose_eq_one_of_mem hk
  have hval := congrArg (fun g : Langlands.GeneralLinear (N + 1) ℂ =>
    (g : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) hg
  simp only [Units.val_mul, Iwasawa.diagonalUnits_val] at hval
  have h1 := congrArg (fun z : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ =>
    ComplexGramFormula.gram l z (z.map (starRingEnd ℂ))) hval
  have hlhs : ComplexGramFormula.gram l
      ((y : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) * (κ : Matrix _ _ ℂ))
      (((y : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) * (κ : Matrix _ _ ℂ)).map
        (starRingEnd ℂ)) = ComplexGramFormula.gram l (y : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
        ((y : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ).map (starRingEnd ℂ)) := by
    rw [Matrix.map_mul, ComplexGramFormula.gram, paddedGram_mul_unitary _ _ _ hκ',
      ← ComplexGramFormula.gram]
  have hrhs : ComplexGramFormula.gram l
      (Matrix.diagonal (fun i => (a i : ℂ)) * ((u : Langlands.GeneralLinear (N + 1) ℂ) :
        Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) * (k : Matrix _ _ ℂ))
      ((Matrix.diagonal (fun i => (a i : ℂ)) * ((u : Langlands.GeneralLinear (N + 1) ℂ) :
        Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) * (k : Matrix _ _ ℂ)).map (starRingEnd ℂ)) =
      ((‖∏ j : Fin (N + 1), if l ≤ (j : ℕ) then (a j : ℂ) else 1‖ ^ 2 : ℝ) : ℂ) := by
    rw [ComplexGramFormula.gram_mul_conj (ComplexGramFormula.isUpperTriangular_diagonal_mul a u)
      hk']
    congr 3
    rw [GramFormula.diagonalTail]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [ComplexGramFormula.diagonal_mul_apply_self]
  rw [hlhs, hrhs] at h1
  exact h1

/-- The real Gram determinant `G_l(y) = Re gram l y ȳ` of the rows `≥ l` of `y`. -/
def gramRe (y : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (l : ℕ) : ℝ :=
  (ComplexGramFormula.gram l y (y.map (starRingEnd ℂ))).re

theorem gramRe_pos (y : Langlands.GeneralLinear (N + 1) ℂ) (l : ℕ) :
    0 < gramRe (y : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) l := by
  obtain ⟨a, u, k, hk, hg⟩ :=
    ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary
      (y * (1 : Langlands.GeneralLinear (N + 1) ℂ))
  have h := prod_tail_sq_eq_gram y 1 (unitaryCompact ℂ (N + 1)).one_mem a u k hk hg l
  rw [gramRe, h, Complex.ofReal_re]
  refine pow_pos (norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun j _ => ?_)) 2
  split_ifs
  · exact (a j).ne_zero
  · exact one_ne_zero

variable {F : Langlands.GeneralLinear (N + 1) ℂ → ℂ} {c : (Fin (N + 1) → ℂˣ) → ℂ} {σ : ℕ → ℝ}

/-- **The general growth bound.** If `F(diag(a) u g) = c(a) F(g)` with `‖c(a)‖ = ∏ |a_l|^{σ_l}`
and `‖F‖ ≤ C` on `U(N+1)`, then for every `y` with `G_0(y) = |det y|² = 1` and `κ ∈ U(N+1)`,
`‖F(y κ)‖ ≤ C ∏_{l<N} G_{l+1}(y)^{(σ_{l+1} − σ_l)/2}`. -/
theorem norm_le_gram
    (hF : ∀ (a : Fin (N + 1) → ℂˣ) (u : upperUnipotent (N + 1) ℂ)
      (g : Langlands.GeneralLinear (N + 1) ℂ),
      F ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear (N + 1) ℂ) *
        (u : Langlands.GeneralLinear (N + 1) ℂ) * g) = c a * F g)
    (hc : ∀ a, ‖c a‖ = ∏ l : Fin (N + 1), ‖(a l : ℂ)‖ ^ σ l)
    {C : ℝ} (hC : ∀ k ∈ unitaryCompact ℂ (N + 1), ‖F k‖ ≤ C)
    (y : Langlands.GeneralLinear (N + 1) ℂ)
    (hy : gramRe (y : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) 0 = 1)
    {κ : Langlands.GeneralLinear (N + 1) ℂ} (hκ : κ ∈ unitaryCompact ℂ (N + 1)) :
    ‖F (y * κ)‖ ≤ C * ∏ l : Fin N,
      gramRe (y : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) ((l : ℕ) + 1) ^
        ((σ ((l : ℕ) + 1) - σ l) / 2) := by
  obtain ⟨a, u, k, hk, hg⟩ :=
    ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary (y * κ)
  rw [hg, hF, norm_mul, hc, mul_comm]
  have hG : ∀ l : ℕ, gramRe (y : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) l =
      ‖∏ j : Fin (N + 1), if l ≤ (j : ℕ) then (a j : ℂ) else 1‖ ^ 2 := fun l => by
    rw [gramRe, prod_tail_sq_eq_gram y κ hκ a u k hk hg l, Complex.ofReal_re]
  have hprod : ∏ l : Fin (N + 1), ‖(a l : ℂ)‖ ^ σ l =
      ∏ l : Fin N, gramRe (y : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) ((l : ℕ) + 1) ^
        ((σ ((l : ℕ) + 1) - σ l) / 2) := by
    have ha : ∀ l, 0 < ‖(a l : ℂ)‖ := fun l => norm_pos_iff.mpr (a l).ne_zero
    set T : ℕ → ℝ := fun l => ∑ j : Fin (N + 1),
      if l ≤ (j : ℕ) then Real.log ‖(a j : ℂ)‖ else 0 with hTdef
    have hT : ∀ l : ℕ, T l =
        Real.log (gramRe (y : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) l) / 2 := by
      intro l
      rw [hG l, Real.log_pow, norm_prod, Real.log_prod]
      · rw [hTdef]
        simp only
        push_cast
        rw [mul_div_cancel_left₀ _ two_ne_zero]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> simp
      · intro j _
        split_ifs
        · exact (ha j).ne'
        · simp
    have hT0 : T 0 = 0 := by rw [hT 0, hy, Real.log_one, zero_div]
    have hsum := sum_mul_eq_sum_sub (t := fun l => Real.log ‖(a l : ℂ)‖) (σ := σ) (T := T)
      (fun l => rfl) hT0
    rw [← Real.exp_log (Finset.prod_pos fun l _ => Real.rpow_pos_of_pos (ha l) _),
      ← Real.exp_log (Finset.prod_pos fun l _ => Real.rpow_pos_of_pos (gramRe_pos y _) _),
      Real.log_prod (fun l _ => (Real.rpow_pos_of_pos (ha l) _).ne'),
      Real.log_prod (fun l _ => (Real.rpow_pos_of_pos (gramRe_pos y _) _).ne')]
    congr 1
    simp only [Real.log_rpow (ha _), Real.log_rpow (gramRe_pos y _)]
    rw [show (∑ l : Fin (N + 1), σ l * Real.log ‖(a l : ℂ)‖) = _ from hsum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hT]
    ring
  rw [hprod]
  exact mul_le_mul_of_nonneg_right (hC k hk)
    (Finset.prod_nonneg fun l _ => (Real.rpow_pos_of_pos (gramRe_pos y _) _).le)

end General

/-! ## Gram determinants of `n̄(X)` -/

section BlockLower

variable {a k : ℕ}

open ComplexBlockParabolic

theorem map_conj_transpose {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) :
    (Z.map (starRingEnd ℂ))ᵀ = Zᴴ := by
  ext i j
  simp [Matrix.conjTranspose_apply]

theorem blockLower_mul_conjTranspose (X : Matrix (Fin k) (Fin a) ℂ) :
    blockLower X * (blockLower X)ᴴ =
      (Matrix.fromBlocks 1 Xᴴ X (X * Xᴴ + 1)).submatrix finSumFinEquiv.symm
        finSumFinEquiv.symm := by
  rw [blockLower, Matrix.conjTranspose_reindex, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp

/-- `X` with the columns `< l` replaced by `0`. -/
def maskCols (l : ℕ) (X : Matrix (Fin k) (Fin a) ℂ) : Matrix (Fin k) (Fin a) ℂ :=
  Matrix.of fun q c => if l ≤ (c : ℕ) then X q c else 0

theorem one_apply_castAdd_natAdd (p : Fin a) (q : Fin k) :
    (1 : Matrix (Fin (a + k)) (Fin (a + k)) ℂ) (Fin.castAdd k p) (Fin.natAdd a q) = 0 := by
  rw [Matrix.one_apply_ne]
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

theorem one_apply_natAdd_castAdd (p : Fin a) (q : Fin k) :
    (1 : Matrix (Fin (a + k)) (Fin (a + k)) ℂ) (Fin.natAdd a q) (Fin.castAdd k p) = 0 := by
  rw [Matrix.one_apply_ne]
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

theorem paddedGram_blockLower_le (X : Matrix (Fin k) (Fin a) ℂ) {l : ℕ} (hl : l ≤ a) :
    ComplexGramFormula.paddedGram l (blockLower X) ((blockLower X).map (starRingEnd ℂ)) =
      (Matrix.fromBlocks 1 (maskCols l X)ᴴ (maskCols l X) (X * Xᴴ + 1)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
  ext i j
  rw [ComplexGramFormula.paddedGram, Matrix.of_apply, map_conj_transpose,
    blockLower_mul_conjTranspose]
  refine Fin.addCases (fun p => ?_) (fun q => ?_) i <;>
    refine Fin.addCases (fun p' => ?_) (fun q' => ?_) j
  · simp only [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
      Matrix.fromBlocks_apply₁₁, Fin.val_castAdd]
    split_ifs
    · rfl
    · rw [Matrix.one_apply, Matrix.one_apply]
      simp [Fin.castAdd_inj]
  · simp only [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₂, Fin.val_castAdd,
      Fin.val_natAdd, maskCols, Matrix.conjTranspose_apply, Matrix.of_apply]
    by_cases hp : l ≤ (p : ℕ)
    · rw [ite_eq_left ⟨hp, by omega⟩, ite_eq_left hp]
    · rw [ite_eq_right (fun h => hp h.1), ite_eq_right hp, one_apply_castAdd_natAdd, star_zero]
  · simp only [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₁, Fin.val_castAdd,
      Fin.val_natAdd, maskCols, Matrix.of_apply]
    by_cases hp : l ≤ (p' : ℕ)
    · rw [ite_eq_left ⟨by omega, hp⟩, ite_eq_left hp]
    · rw [ite_eq_right (fun h => hp h.2), ite_eq_right hp, one_apply_natAdd_castAdd]
  · simp only [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
      Matrix.fromBlocks_apply₂₂, Fin.val_natAdd]
    rw [ite_eq_left ⟨by omega, by omega⟩]

theorem sum_castLE {l : ℕ} (hl : l ≤ a) (g : Fin a → ℂ) :
    ∑ c : Fin l, g (Fin.castLE hl c) = ∑ c : Fin a, if (c : ℕ) < l then g c else 0 := by
  rw [← Finset.sum_filter]
  have h : (Finset.univ.filter fun c : Fin a => (c : ℕ) < l) =
      Finset.univ.map (Fin.castLEEmb hl) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Fin.castLEEmb_apply]
    constructor
    · intro hc
      exact ⟨⟨c, hc⟩, Fin.ext rfl⟩
    · rintro ⟨c', rfl⟩
      simp
  rw [h, Finset.sum_map]
  rfl

/-- The columns `< l` of `X`. -/
def colsBelow (X : Matrix (Fin k) (Fin a) ℂ) {l : ℕ} (hl : l ≤ a) : Matrix (Fin k) (Fin l) ℂ :=
  X.submatrix id (Fin.castLE hl)

theorem sub_maskCols (X : Matrix (Fin k) (Fin a) ℂ) {l : ℕ} (hl : l ≤ a) :
    X * Xᴴ + 1 - maskCols l X * (maskCols l X)ᴴ = 1 + colsBelow X hl * (colsBelow X hl)ᴴ := by
  ext q q'
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    maskCols, Matrix.of_apply, colsBelow, Matrix.submatrix_apply, id]
  rw [sum_castLE hl (fun c => X q c * star (X q' c))]
  have hc : ∀ c : Fin a, X q c * star (X q' c) -
      (if l ≤ (c : ℕ) then X q c else 0) * star (if l ≤ (c : ℕ) then X q' c else 0) =
      if (c : ℕ) < l then X q c * star (X q' c) else 0 := by
    intro c
    by_cases h : l ≤ (c : ℕ)
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_right (by omega), sub_self]
    · rw [ite_eq_right h, ite_eq_right h, ite_eq_left (by omega), star_zero, mul_zero, sub_zero]
  rw [← Finset.sum_congr rfl fun c _ => hc c, Finset.sum_sub_distrib]
  ring

theorem gram_blockLower_le (X : Matrix (Fin k) (Fin a) ℂ) {l : ℕ} (hl : l ≤ a) :
    ComplexGramFormula.gram l (blockLower X) ((blockLower X).map (starRingEnd ℂ)) =
      (1 + colsBelow X hl * (colsBelow X hl)ᴴ).det := by
  rw [ComplexGramFormula.gram, paddedGram_blockLower_le X hl, Matrix.det_submatrix_equiv_self,
    Matrix.det_fromBlocks_one₁₁, sub_maskCols X hl]

/-- `M` on the indices `≥ j` and the identity elsewhere. -/
def padFrom (j : ℕ) (M : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of fun q q' => if j ≤ (q : ℕ) ∧ j ≤ (q' : ℕ) then M q q' else (1 : Matrix _ _ ℂ) q q'

theorem paddedGram_blockLower_ge (X : Matrix (Fin k) (Fin a) ℂ) (j : ℕ) :
    ComplexGramFormula.paddedGram (a + j) (blockLower X) ((blockLower X).map (starRingEnd ℂ)) =
      (Matrix.fromBlocks 1 0 0 (padFrom j (X * Xᴴ + 1))).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
  ext i i'
  rw [ComplexGramFormula.paddedGram, Matrix.of_apply, map_conj_transpose,
    blockLower_mul_conjTranspose]
  refine Fin.addCases (fun p => ?_) (fun q => ?_) i <;>
    refine Fin.addCases (fun p' => ?_) (fun q' => ?_) i'
  · simp only [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
      Matrix.fromBlocks_apply₁₁, Fin.val_castAdd]
    rw [ite_eq_right (by omega), Matrix.one_apply, Matrix.one_apply]
    simp [Fin.castAdd_inj]
  · simp only [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₂, Fin.val_castAdd,
      Fin.val_natAdd]
    rw [ite_eq_right (by omega), one_apply_castAdd_natAdd, Matrix.zero_apply]
  · simp only [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₁, Fin.val_castAdd,
      Fin.val_natAdd]
    rw [ite_eq_right (by omega), one_apply_natAdd_castAdd, Matrix.zero_apply]
  · simp only [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
      Matrix.fromBlocks_apply₂₂, Fin.val_natAdd, padFrom, Matrix.of_apply]
    by_cases h : j ≤ (q : ℕ) ∧ j ≤ (q' : ℕ)
    · rw [ite_eq_left ⟨by omega, by omega⟩, ite_eq_left h]
    · rw [ite_eq_right (fun h' => h ⟨by omega, by omega⟩), ite_eq_right h, Matrix.one_apply,
        Matrix.one_apply]
      simp [Fin.natAdd_inj]

/-- The rows `j, j+1, …` of a `k`-indexed object, `Fin (k - j) → Fin k`. -/
def fromIdx {j : ℕ} (hj : j ≤ k) (i : Fin (k - j)) : Fin k := ⟨j + i, by omega⟩

theorem det_padFrom (M : Matrix (Fin k) (Fin k) ℂ) {j : ℕ} (hj : j ≤ k) :
    (padFrom j M).det = (M.submatrix (fromIdx hj) (fromIdx hj)).det := by
  set e : Fin j ⊕ Fin (k - j) ≃ Fin k := finSumFinEquiv.trans (finCongr (by omega))
  have he_inl : ∀ i : Fin j, (e (Sum.inl i) : ℕ) = i := fun i => by simp [e]
  have he_inr : ∀ i : Fin (k - j), (e (Sum.inr i) : ℕ) = j + i := fun i => by simp [e]
  have hfrom : ∀ i : Fin (k - j), e (Sum.inr i) = fromIdx hj i := fun i =>
    Fin.ext (by rw [he_inr]; rfl)
  have h : padFrom j M = (Matrix.fromBlocks 1 0 0 (M.submatrix (fromIdx hj) (fromIdx hj))).submatrix
      e.symm e.symm := by
    ext q q'
    obtain ⟨s, rfl⟩ := e.surjective q
    obtain ⟨s', rfl⟩ := e.surjective q'
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, padFrom, Matrix.of_apply]
    rcases s with i | i <;> rcases s' with i' | i'
    · rw [Matrix.fromBlocks_apply₁₁, ite_eq_right (by rw [he_inl]; omega), Matrix.one_apply,
        Matrix.one_apply]
      simp [e.injective.eq_iff]
    · rw [Matrix.fromBlocks_apply₁₂, ite_eq_right (by rw [he_inl]; omega), Matrix.zero_apply,
        Matrix.one_apply_ne]
      intro h'
      have := e.injective h'
      simp at this
    · rw [Matrix.fromBlocks_apply₂₁, ite_eq_right (by rw [he_inl]; omega), Matrix.zero_apply,
        Matrix.one_apply_ne]
      intro h'
      have := e.injective h'
      simp at this
    · rw [Matrix.fromBlocks_apply₂₂, ite_eq_left ⟨by rw [he_inr]; omega, by rw [he_inr]; omega⟩,
        hfrom, hfrom, Matrix.submatrix_apply]
  rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul]

/-- The rows `≥ j` of `X`. -/
def rowsGe (X : Matrix (Fin k) (Fin a) ℂ) {j : ℕ} (hj : j ≤ k) : Matrix (Fin (k - j)) (Fin a) ℂ :=
  X.submatrix (fromIdx hj) id

theorem gram_blockLower_ge (X : Matrix (Fin k) (Fin a) ℂ) {j : ℕ} (hj : j ≤ k) :
    ComplexGramFormula.gram (a + j) (blockLower X) ((blockLower X).map (starRingEnd ℂ)) =
      (1 + rowsGe X hj * (rowsGe X hj)ᴴ).det := by
  rw [ComplexGramFormula.gram, paddedGram_blockLower_ge X j, Matrix.det_submatrix_equiv_self,
    Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul, det_padFrom _ hj]
  congr 1
  have hinj : Function.Injective (fromIdx hj) := fun i i' h => by
    have := congrArg Fin.val h
    simp only [fromIdx] at this
    exact Fin.ext (by omega)
  ext q q'
  simp only [Matrix.submatrix_apply, Matrix.add_apply, rowsGe, Matrix.mul_apply,
    Matrix.conjTranspose_apply, id, Matrix.one_apply, hinj.eq_iff]
  ring

end BlockLower

/-! ## The block chart bound -/

section Bound

variable {a k : ℕ}

open ComplexBlockParabolic

theorem blockLowerGL_val (X : Matrix (Fin k) (Fin a) ℂ) :
    ((blockLowerGL X : Langlands.GeneralLinear (a + k) ℂ) :
      Matrix (Fin (a + k)) (Fin (a + k)) ℂ) = blockLower X := IsUnit.unit_spec _

theorem gramRe_blockLower_col (X : Matrix (Fin (k + 1)) (Fin a) ℂ) (l : Fin a) :
    gramRe (N := a + k) (blockLower (a := a) (k := k + 1) X) ((l : ℕ) + 1) =
      ComplexBlockChart.colGram X l := by
  have hl : (l : ℕ) + 1 ≤ a := l.isLt
  rw [gramRe, gram_blockLower_le X hl, ComplexBlockChart.colGram, Matrix.det_one_add_mul_comm]
  rfl

theorem gramRe_blockLower_row (X : Matrix (Fin (k + 1)) (Fin a) ℂ) (j : Fin k) :
    gramRe (N := a + k) (blockLower (a := a) (k := k + 1) X) (a + ((j : ℕ) + 1)) =
      ComplexBlockChart.rowGram X j.succ := by
  have hj : (j : ℕ) + 1 ≤ k + 1 := by omega
  rw [gramRe, gram_blockLower_ge X hj, ComplexBlockChart.rowGram]
  rfl

theorem gramRe_blockLower_zero (X : Matrix (Fin (k + 1)) (Fin a) ℂ) :
    gramRe (N := a + k) (blockLower (a := a) (k := k + 1) X) 0 = 1 := by
  rw [gramRe, gram_blockLower_le X (Nat.zero_le a)]
  have : colsBelow X (Nat.zero_le a) * (colsBelow X (Nat.zero_le a))ᴴ = 0 := by
    ext q q'
    simp [Matrix.mul_apply]
  rw [this, add_zero, Matrix.det_one, Complex.one_re]

variable {F : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ} {c : (Fin (a + (k + 1)) → ℂˣ) → ℂ}
  {σ : ℕ → ℝ}

/-- **The block chart bound with a tied last block.** If `F(diag(z) u g) = c(z) F(g)` with
`‖c(z)‖ = ∏ |z_l|^{σ_l}`, `‖F‖ ≤ C` on `U(a+k+1)`, and `(σ_{a+j} − σ_{a+j−1})/2 = −1` for
`1 ≤ j ≤ k`, then `‖F(n̄(X) κ)‖ ≤ C · blockChartBound ε X` with `ε_l = (σ_{l+1} − σ_l)/2`. -/
theorem norm_le_blockChartBound
    (hF : ∀ (z : Fin (a + (k + 1)) → ℂˣ) (u : upperUnipotent (a + (k + 1)) ℂ)
      (g : Langlands.GeneralLinear (a + (k + 1)) ℂ),
      F ((Iwasawa.diagonalUnits z : Langlands.GeneralLinear (a + (k + 1)) ℂ) *
        (u : Langlands.GeneralLinear (a + (k + 1)) ℂ) * g) = c z * F g)
    (hc : ∀ z, ‖c z‖ = ∏ l : Fin (a + (k + 1)), ‖(z l : ℂ)‖ ^ σ l)
    {C : ℝ} (hC : ∀ κ ∈ unitaryCompact ℂ (a + (k + 1)), ‖F κ‖ ≤ C)
    (hσ : ∀ j : ℕ, 1 ≤ j → j ≤ k → (σ (a + j) - σ (a + j - 1)) / 2 = -1)
    (X : Matrix (Fin (k + 1)) (Fin a) ℂ) {κ : Langlands.GeneralLinear (a + (k + 1)) ℂ}
    (hκ : κ ∈ unitaryCompact ℂ (a + (k + 1))) :
    ‖F (blockLowerGL (a := a) (k := k + 1) X * κ)‖ ≤
      C * ComplexBlockChart.blockChartBound (fun l : Fin a => (σ ((l : ℕ) + 1) - σ l) / 2) X := by
  have h := norm_le_gram (N := a + k) hF hc hC (blockLowerGL (a := a) (k := k + 1) X)
    (by rw [blockLowerGL_val]; exact gramRe_blockLower_zero X) hκ
  refine h.trans (le_of_eq ?_)
  congr 1
  rw [Fin.prod_univ_add, ComplexBlockChart.blockChartBound, Fin.prod_univ_succ]
  simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_zero, Fin.val_succ, blockLowerGL_val]
  congr 1
  · refine Finset.prod_congr rfl fun l _ => ?_
    rw [gramRe_blockLower_col]
  · rw [ite_true, one_mul]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [ite_eq_right (by omega), show a + (j : ℕ) + 1 = a + ((j : ℕ) + 1) by ring,
      gramRe_blockLower_row, show σ (a + ((j : ℕ) + 1)) = σ (a + ((j : ℕ) + 1)) from rfl]
    have := hσ ((j : ℕ) + 1) (by omega) (by omega)
    rw [show a + ((j : ℕ) + 1) - 1 = a + (j : ℕ) by omega] at this
    rw [show (σ (a + ((j : ℕ) + 1)) - σ (a + (j : ℕ))) / 2 = -1 from this, Real.rpow_neg_one]

end Bound

end ComplexBlockChart

open ComplexBlockParabolic in
/-- **Statement (growth along the opposite unipotent radical of `P_{a,k+1}` with a tied last
block).** Let `F : GL_{a+k+1}(ℂ) → ℂ`, `c : (ℂˣ)^{a+k+1} → ℂ` and `σ : ℕ → ℝ` satisfy
`F(diag(z) u g) = c(z) F(g)` for upper unipotent `u` and `‖c(z)‖ = ∏_l |z_l|^{σ_l}`, let
`‖F(κ)‖ ≤ C` on `U(a+k+1)`, and let `(σ_{a+j} − σ_{a+j−1})/2 = −1` for `1 ≤ j ≤ k`. Then for every
`X ∈ M_{(k+1)×a}(ℂ)` and `κ ∈ U(a+k+1)`,
`‖F(n̄(X) κ)‖ ≤ C ∏_{l<a} det(1 + X_{≤l}ᴴ X_{≤l})^{(σ_{l+1} − σ_l)/2} ∏_{1 ≤ j ≤ k} det(1 + X^{(j)} X^{(j)ᴴ})^{−1}`
(`ComplexBlockChart.blockChartBound`), where `n̄(X) = [[1, 0], [X, 1]]`. -/
def ComplexBlockChartBoundStatement : Prop :=
  ∀ (a k : ℕ) (F : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ)
    (c : (Fin (a + (k + 1)) → ℂˣ) → ℂ) (σ : ℕ → ℝ),
    (∀ (z : Fin (a + (k + 1)) → ℂˣ) (u : Langlands.GeneralLinear.upperUnipotent (a + (k + 1)) ℂ)
      (g : Langlands.GeneralLinear (a + (k + 1)) ℂ),
      F ((Langlands.GeneralLinear.Iwasawa.diagonalUnits z :
          Langlands.GeneralLinear (a + (k + 1)) ℂ) *
        (u : Langlands.GeneralLinear (a + (k + 1)) ℂ) * g) = c z * F g) →
    (∀ z, ‖c z‖ = ∏ l : Fin (a + (k + 1)), ‖(z l : ℂ)‖ ^ σ l) →
    ∀ C : ℝ, (∀ κ ∈ unitaryCompact ℂ (a + (k + 1)), ‖F κ‖ ≤ C) →
    (∀ j : ℕ, 1 ≤ j → j ≤ k → (σ (a + j) - σ (a + j - 1)) / 2 = -1) →
    ∀ (X : Matrix (Fin (k + 1)) (Fin a) ℂ) (κ : Langlands.GeneralLinear (a + (k + 1)) ℂ),
      κ ∈ unitaryCompact ℂ (a + (k + 1)) →
      ‖F (blockLowerGL (a := a) (k := k + 1) X * κ)‖ ≤
        C * ComplexBlockChart.blockChartBound (fun l : Fin a => (σ ((l : ℕ) + 1) - σ l) / 2) X

theorem complexBlockChartBound : ComplexBlockChartBoundStatement := by
  intro a k F c σ hF hc C hC hσ X κ hκ
  exact ComplexBlockChart.norm_le_blockChartBound hF hc hC hσ X hκ

end Langlands.Archimedean
