import Langlands.Representation.Archimedean.ParabolicChartBound
import Langlands.Representation.Archimedean.RealBlockChartIntegralStatement
import Langlands.Representation.Archimedean.RealBlockParabolicIntegrationStatement

/-!
# Growth of real principal-series functions along the opposite unipotent radical of `P_{a,k}`

`RealBlockChart.norm_le_gram`: a function `F` of a principal series of `GL_{N+1}(ℝ)` bounded by
`C` on `O(N+1)` satisfies `‖F(y κ)‖ ≤ C ∏_{l ≥ 1} G_l(y)^{(σ_l − σ_{l−1})/2}` for every `y` with
`det(y)² = 1`, where `G_l(y)` are the Gram determinants of the lower rows of `y`.
`RealBlockChart.gram_blockLower_le` and `gram_blockLower_ge` compute them for
`y = n̄(X) = [[1, 0], [X, 1]]`, and `norm_le_blockChartBound` combines both when the last block is
tied.
-/

noncomputable section

open MeasureTheory Matrix

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace RealBlockChart

open MaximalParabolicIntegration ParabolicChartBound GramFormula Langlands.GeneralLinear

/-! ## The general growth bound -/

section General

variable {N : ℕ}

theorem prod_tail_sq_eq_gram (y κ : Langlands.GeneralLinear (N + 1) ℝ)
    (hκ : κ ∈ unitaryCompact ℝ (N + 1)) (a : Fin (N + 1) → ℝˣ) (u : upperUnipotent (N + 1) ℝ)
    (k : Langlands.GeneralLinear (N + 1) ℝ) (hk : k ∈ unitaryCompact ℝ (N + 1))
    (hg : y * κ = (Iwasawa.diagonalUnits a : Langlands.GeneralLinear (N + 1) ℝ) *
      (u : Langlands.GeneralLinear (N + 1) ℝ) * k) (l : ℕ) :
    gram l (y : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) =
      (∏ j : Fin (N + 1), if l ≤ (j : ℕ) then (a j : ℝ) else 1) ^ 2 := by
  have hκ' := mul_transpose_eq_one_of_mem hκ
  have hk' := mul_transpose_eq_one_of_mem hk
  have hval := congrArg (fun g : Langlands.GeneralLinear (N + 1) ℝ =>
    (g : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)) hg
  simp only [Units.val_mul, Iwasawa.diagonalUnits_val] at hval
  have h1 := congrArg (gram l) hval
  rw [gram_mul_orthogonal _ _ hκ', gram_diagonal_mul _ _ _ u.2.1 u.2.2 hk'] at h1
  exact h1

variable {F : Langlands.GeneralLinear (N + 1) ℝ → ℂ} {c : (Fin (N + 1) → ℝˣ) → ℂ} {σ : ℕ → ℝ}

/-- **The general growth bound.** If `F(diag(a) u g) = c(a) F(g)` with `‖c(a)‖ = ∏ |a_l|^{σ_l}`
and `‖F‖ ≤ C` on `O(N+1)`, then for every `y` with `G_0(y) = det(y)² = 1` and `κ ∈ O(N+1)`,
`‖F(y κ)‖ ≤ C ∏_{l<N} G_{l+1}(y)^{(σ_{l+1} − σ_l)/2}`. -/
theorem norm_le_gram
    (hF : ∀ (a : Fin (N + 1) → ℝˣ) (u : upperUnipotent (N + 1) ℝ)
      (g : Langlands.GeneralLinear (N + 1) ℝ),
      F ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear (N + 1) ℝ) *
        (u : Langlands.GeneralLinear (N + 1) ℝ) * g) = c a * F g)
    (hc : ∀ a, ‖c a‖ = ∏ l : Fin (N + 1), |(a l : ℝ)| ^ σ l)
    {C : ℝ} (hC : ∀ k ∈ unitaryCompact ℝ (N + 1), ‖F k‖ ≤ C)
    (y : Langlands.GeneralLinear (N + 1) ℝ)
    (hy : gram 0 (y : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) = 1)
    {κ : Langlands.GeneralLinear (N + 1) ℝ} (hκ : κ ∈ unitaryCompact ℝ (N + 1)) :
    ‖F (y * κ)‖ ≤ C * ∏ l : Fin N,
      gram ((l : ℕ) + 1) (y : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) ^
        ((σ ((l : ℕ) + 1) - σ l) / 2) := by
  obtain ⟨a, u, k, hk, hg⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact (y * κ)
  rw [hg, hF, norm_mul, hc, mul_comm]
  have hprod : ∏ l : Fin (N + 1), |(a l : ℝ)| ^ σ l =
      ∏ l : Fin N, gram ((l : ℕ) + 1) (y : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) ^
        ((σ ((l : ℕ) + 1) - σ l) / 2) := by
    have ha : ∀ l, 0 < |(a l : ℝ)| := fun l => abs_pos.mpr (a l).ne_zero
    set T : ℕ → ℝ := fun l => ∑ j : Fin (N + 1),
      if l ≤ (j : ℕ) then Real.log |(a j : ℝ)| else 0 with hTdef
    have hT : ∀ l : ℕ,
        T l = Real.log (gram l (y : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)) / 2 := by
      intro l
      rw [prod_tail_sq_eq_gram y κ hκ a u k hk hg l, Real.log_pow, ← Real.log_abs,
        Finset.abs_prod, Real.log_prod]
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
    have hsum := sum_mul_eq_sum_sub (t := fun l => Real.log |(a l : ℝ)|) (σ := σ) (T := T)
      (fun l => rfl) hT0
    rw [← Real.exp_log (Finset.prod_pos fun l _ => Real.rpow_pos_of_pos (ha l) _),
      ← Real.exp_log (Finset.prod_pos fun l _ => Real.rpow_pos_of_pos (gram_pos y _) _),
      Real.log_prod (fun l _ => (Real.rpow_pos_of_pos (ha l) _).ne'),
      Real.log_prod (fun l _ => (Real.rpow_pos_of_pos (gram_pos y _) _).ne')]
    congr 1
    simp only [Real.log_rpow (ha _), Real.log_rpow (gram_pos y _)]
    rw [show (∑ l : Fin (N + 1), σ l * Real.log |(a l : ℝ)|) = _ from hsum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hT]
    ring
  rw [hprod]
  exact mul_le_mul_of_nonneg_right (hC k hk)
    (Finset.prod_nonneg fun l _ => (Real.rpow_pos_of_pos (gram_pos y _) _).le)

end General

/-! ## Gram determinants of `n̄(X)` -/

section BlockLower

variable {a k : ℕ}

open RealBlockParabolic

theorem blockLower_mul_transpose (X : Matrix (Fin k) (Fin a) ℝ) :
    blockLower X * (blockLower X)ᵀ =
      (Matrix.fromBlocks 1 Xᵀ X (X * Xᵀ + 1)).submatrix finSumFinEquiv.symm
        finSumFinEquiv.symm := by
  rw [blockLower, Matrix.transpose_reindex, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp

/-- `X` with the columns `< l` replaced by `0`. -/
def maskCols (l : ℕ) (X : Matrix (Fin k) (Fin a) ℝ) : Matrix (Fin k) (Fin a) ℝ :=
  Matrix.of fun q c => if l ≤ (c : ℕ) then X q c else 0

theorem one_apply_castAdd_natAdd (p : Fin a) (q : Fin k) :
    (1 : Matrix (Fin (a + k)) (Fin (a + k)) ℝ) (Fin.castAdd k p) (Fin.natAdd a q) = 0 := by
  rw [Matrix.one_apply_ne]
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

theorem one_apply_natAdd_castAdd (p : Fin a) (q : Fin k) :
    (1 : Matrix (Fin (a + k)) (Fin (a + k)) ℝ) (Fin.natAdd a q) (Fin.castAdd k p) = 0 := by
  rw [Matrix.one_apply_ne]
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

theorem paddedGram_blockLower_le (X : Matrix (Fin k) (Fin a) ℝ) {l : ℕ} (hl : l ≤ a) :
    paddedGram l (blockLower X) =
      (Matrix.fromBlocks 1 (maskCols l X)ᵀ (maskCols l X) (X * Xᵀ + 1)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
  ext i j
  rw [paddedGram, Matrix.of_apply, blockLower_mul_transpose]
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
      Fin.val_natAdd, maskCols, Matrix.transpose_apply, Matrix.of_apply]
    by_cases hp : l ≤ (p : ℕ)
    · rw [ite_eq_left ⟨hp, by omega⟩, ite_eq_left hp]
    · rw [ite_eq_right (fun h => hp h.1), ite_eq_right hp, one_apply_castAdd_natAdd]
  · simp only [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₁, Fin.val_castAdd,
      Fin.val_natAdd, maskCols, Matrix.of_apply]
    by_cases hp : l ≤ (p' : ℕ)
    · rw [ite_eq_left ⟨by omega, hp⟩, ite_eq_left hp]
    · rw [ite_eq_right (fun h => hp h.2), ite_eq_right hp, one_apply_natAdd_castAdd]
  · simp only [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
      Matrix.fromBlocks_apply₂₂, Fin.val_natAdd]
    rw [ite_eq_left ⟨by omega, by omega⟩]

theorem sum_castLE {l : ℕ} (hl : l ≤ a) (g : Fin a → ℝ) :
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
def colsBelow (X : Matrix (Fin k) (Fin a) ℝ) {l : ℕ} (hl : l ≤ a) : Matrix (Fin k) (Fin l) ℝ :=
  X.submatrix id (Fin.castLE hl)

theorem sub_maskCols (X : Matrix (Fin k) (Fin a) ℝ) {l : ℕ} (hl : l ≤ a) :
    X * Xᵀ + 1 - maskCols l X * (maskCols l X)ᵀ = 1 + colsBelow X hl * (colsBelow X hl)ᵀ := by
  ext q q'
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
    maskCols, Matrix.of_apply, colsBelow, Matrix.submatrix_apply, id]
  rw [sum_castLE hl (fun c => X q c * X q' c)]
  have hc : ∀ c : Fin a, X q c * X q' c -
      (if l ≤ (c : ℕ) then X q c else 0) * (if l ≤ (c : ℕ) then X q' c else 0) =
      if (c : ℕ) < l then X q c * X q' c else 0 := by
    intro c
    by_cases h : l ≤ (c : ℕ)
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_right (by omega), sub_self]
    · rw [ite_eq_right h, ite_eq_right h, ite_eq_left (by omega), mul_zero, sub_zero]
  rw [← Finset.sum_congr rfl fun c _ => hc c, Finset.sum_sub_distrib]
  ring

theorem gram_blockLower_le (X : Matrix (Fin k) (Fin a) ℝ) {l : ℕ} (hl : l ≤ a) :
    gram l (blockLower X) = (1 + colsBelow X hl * (colsBelow X hl)ᵀ).det := by
  rw [gram, paddedGram_blockLower_le X hl, Matrix.det_submatrix_equiv_self,
    Matrix.det_fromBlocks_one₁₁, sub_maskCols X hl]

/-- `M` on the indices `≥ j` and the identity elsewhere. -/
def padFrom (j : ℕ) (M : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun q q' => if j ≤ (q : ℕ) ∧ j ≤ (q' : ℕ) then M q q' else (1 : Matrix _ _ ℝ) q q'

theorem paddedGram_blockLower_ge (X : Matrix (Fin k) (Fin a) ℝ) (j : ℕ) :
    paddedGram (a + j) (blockLower X) =
      (Matrix.fromBlocks 1 0 0 (padFrom j (X * Xᵀ + 1))).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
  ext i i'
  rw [paddedGram, Matrix.of_apply, blockLower_mul_transpose]
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

theorem det_padFrom (M : Matrix (Fin k) (Fin k) ℝ) {j : ℕ} (hj : j ≤ k) :
    (padFrom j M).det = (M.submatrix (fromIdx hj) (fromIdx hj)).det := by
  set e : Fin j ⊕ Fin (k - j) ≃ Fin k := finSumFinEquiv.trans (finCongr (by omega))
  have he_inl : ∀ i : Fin j, (e (Sum.inl i) : ℕ) = i := fun i => by simp [e]
  have he_inr : ∀ i : Fin (k - j), (e (Sum.inr i) : ℕ) = j + i := fun i => by simp [e]
  have hfrom : ∀ i : Fin (k - j), e (Sum.inr i) = fromIdx hj i := fun i =>
    Fin.ext (by rw [he_inr]; rfl)
  have h : padFrom j M =
      (Matrix.fromBlocks 1 0 0 (M.submatrix (fromIdx hj) (fromIdx hj))).submatrix
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
def rowsGe (X : Matrix (Fin k) (Fin a) ℝ) {j : ℕ} (hj : j ≤ k) :
    Matrix (Fin (k - j)) (Fin a) ℝ :=
  X.submatrix (fromIdx hj) id

theorem gram_blockLower_ge (X : Matrix (Fin k) (Fin a) ℝ) {j : ℕ} (hj : j ≤ k) :
    gram (a + j) (blockLower X) = (1 + rowsGe X hj * (rowsGe X hj)ᵀ).det := by
  rw [gram, paddedGram_blockLower_ge X j, Matrix.det_submatrix_equiv_self,
    Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul, det_padFrom _ hj]
  congr 1
  have hinj : Function.Injective (fromIdx hj) := fun i i' h => by
    have := congrArg Fin.val h
    simp only [fromIdx] at this
    exact Fin.ext (by omega)
  ext q q'
  simp only [Matrix.submatrix_apply, Matrix.add_apply, rowsGe, Matrix.mul_apply,
    Matrix.transpose_apply, id, Matrix.one_apply, hinj.eq_iff]
  ring

end BlockLower

/-! ## The block chart bound -/

section Bound

variable {a k : ℕ}

open RealBlockParabolic

theorem blockLowerGL_val (X : Matrix (Fin k) (Fin a) ℝ) :
    ((blockLowerGL X : Langlands.GeneralLinear (a + k) ℝ) :
      Matrix (Fin (a + k)) (Fin (a + k)) ℝ) = blockLower X := IsUnit.unit_spec _

theorem gram_blockLower_col (X : Matrix (Fin (k + 1)) (Fin a) ℝ) (l : Fin a) :
    gram (n := a + k + 1) ((l : ℕ) + 1) (blockLower (a := a) (k := k + 1) X) = colGram X l := by
  have hl : (l : ℕ) + 1 ≤ a := l.isLt
  rw [gram_blockLower_le X hl, colGram, Matrix.det_one_add_mul_comm]
  rfl

theorem gram_blockLower_row (X : Matrix (Fin (k + 1)) (Fin a) ℝ) (j : Fin k) :
    gram (n := a + k + 1) (a + ((j : ℕ) + 1)) (blockLower (a := a) (k := k + 1) X) =
      rowGram X j.succ := by
  have hj : (j : ℕ) + 1 ≤ k + 1 := by omega
  rw [gram_blockLower_ge X hj, rowGram]
  rfl

theorem gram_blockLower_zero (X : Matrix (Fin (k + 1)) (Fin a) ℝ) :
    gram (n := a + k + 1) 0 (blockLower (a := a) (k := k + 1) X) = 1 := by
  rw [gram_blockLower_le X (Nat.zero_le a)]
  have : colsBelow X (Nat.zero_le a) * (colsBelow X (Nat.zero_le a))ᵀ = 0 := by
    ext q q'
    simp [Matrix.mul_apply]
  rw [this, add_zero, Matrix.det_one]

variable {F : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ} {c : (Fin (a + (k + 1)) → ℝˣ) → ℂ}
  {σ : ℕ → ℝ}

/-- **The block chart bound with a tied last block.** If `F(diag(z) u g) = c(z) F(g)` with
`‖c(z)‖ = ∏ |z_l|^{σ_l}`, `‖F‖ ≤ C` on `O(a+k+1)`, and `(σ_{a+j} − σ_{a+j−1})/2 = −1/2` for
`1 ≤ j ≤ k`, then `‖F(n̄(X) κ)‖ ≤ C · blockChartBound ε X` with `ε_l = (σ_{l+1} − σ_l)/2`. -/
theorem norm_le_blockChartBound
    (hF : ∀ (z : Fin (a + (k + 1)) → ℝˣ) (u : upperUnipotent (a + (k + 1)) ℝ)
      (g : Langlands.GeneralLinear (a + (k + 1)) ℝ),
      F ((Iwasawa.diagonalUnits z : Langlands.GeneralLinear (a + (k + 1)) ℝ) *
        (u : Langlands.GeneralLinear (a + (k + 1)) ℝ) * g) = c z * F g)
    (hc : ∀ z, ‖c z‖ = ∏ l : Fin (a + (k + 1)), |(z l : ℝ)| ^ σ l)
    {C : ℝ} (hC : ∀ κ ∈ unitaryCompact ℝ (a + (k + 1)), ‖F κ‖ ≤ C)
    (hσ : ∀ j : ℕ, 1 ≤ j → j ≤ k → (σ (a + j) - σ (a + j - 1)) / 2 = -(1 / 2))
    (X : Matrix (Fin (k + 1)) (Fin a) ℝ) {κ : Langlands.GeneralLinear (a + (k + 1)) ℝ}
    (hκ : κ ∈ unitaryCompact ℝ (a + (k + 1))) :
    ‖F (blockLowerGL (a := a) (k := k + 1) X * κ)‖ ≤
      C * blockChartBound (fun l : Fin a => (σ ((l : ℕ) + 1) - σ l) / 2) X := by
  have h := norm_le_gram (N := a + k) hF hc hC (blockLowerGL (a := a) (k := k + 1) X)
    (by rw [blockLowerGL_val]; exact gram_blockLower_zero X) hκ
  refine h.trans (le_of_eq ?_)
  congr 1
  rw [Fin.prod_univ_add, blockChartBound, Fin.prod_univ_succ]
  simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_zero, Fin.val_succ, blockLowerGL_val]
  congr 1
  · refine Finset.prod_congr rfl fun l _ => ?_
    rw [gram_blockLower_col]
  · rw [ite_true, one_mul]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [ite_eq_right (by omega), show a + (j : ℕ) + 1 = a + ((j : ℕ) + 1) by ring,
      gram_blockLower_row]
    have := hσ ((j : ℕ) + 1) (by omega) (by omega)
    rw [show a + ((j : ℕ) + 1) - 1 = a + (j : ℕ) by omega] at this
    rw [show (σ (a + ((j : ℕ) + 1)) - σ (a + (j : ℕ))) / 2 = -(1 / 2) from this]

end Bound

end RealBlockChart

open RealBlockParabolic in
/-- **Statement (growth along the opposite unipotent radical of `P_{a,k+1}` with a tied last
block).** Let `F : GL_{a+k+1}(ℝ) → ℂ`, `c : (ℝˣ)^{a+k+1} → ℂ` and `σ : ℕ → ℝ` satisfy
`F(diag(z) u g) = c(z) F(g)` for upper unipotent `u` and `‖c(z)‖ = ∏_l |z_l|^{σ_l}`, let
`‖F(κ)‖ ≤ C` on `O(a+k+1)`, and let `(σ_{a+j} − σ_{a+j−1})/2 = −1/2` for `1 ≤ j ≤ k`. Then for
every `X ∈ M_{(k+1)×a}(ℝ)` and `κ ∈ O(a+k+1)`,
`‖F(n̄(X) κ)‖ ≤ C ∏_{l<a} det(1 + X_{≤l}ᵀ X_{≤l})^{(σ_{l+1} − σ_l)/2} ∏_{1 ≤ j ≤ k} det(1 + X^{(j)} X^{(j)ᵀ})^{−1/2}`
(`RealBlockChart.blockChartBound`), where `n̄(X) = [[1, 0], [X, 1]]`. -/
def RealBlockChartBoundStatement : Prop :=
  ∀ (a k : ℕ) (F : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ)
    (c : (Fin (a + (k + 1)) → ℝˣ) → ℂ) (σ : ℕ → ℝ),
    (∀ (z : Fin (a + (k + 1)) → ℝˣ) (u : Langlands.GeneralLinear.upperUnipotent (a + (k + 1)) ℝ)
      (g : Langlands.GeneralLinear (a + (k + 1)) ℝ),
      F ((Langlands.GeneralLinear.Iwasawa.diagonalUnits z :
          Langlands.GeneralLinear (a + (k + 1)) ℝ) *
        (u : Langlands.GeneralLinear (a + (k + 1)) ℝ) * g) = c z * F g) →
    (∀ z, ‖c z‖ = ∏ l : Fin (a + (k + 1)), |(z l : ℝ)| ^ σ l) →
    ∀ C : ℝ, (∀ κ ∈ unitaryCompact ℝ (a + (k + 1)), ‖F κ‖ ≤ C) →
    (∀ j : ℕ, 1 ≤ j → j ≤ k → (σ (a + j) - σ (a + j - 1)) / 2 = -(1 / 2)) →
    ∀ (X : Matrix (Fin (k + 1)) (Fin a) ℝ) (κ : Langlands.GeneralLinear (a + (k + 1)) ℝ),
      κ ∈ unitaryCompact ℝ (a + (k + 1)) →
      ‖F (blockLowerGL (a := a) (k := k + 1) X * κ)‖ ≤
        C * RealBlockChart.blockChartBound (fun l : Fin a => (σ ((l : ℕ) + 1) - σ l) / 2) X

theorem realBlockChartBound : RealBlockChartBoundStatement := by
  intro a k F c σ hF hc C hC hσ X κ hκ
  exact RealBlockChart.norm_le_blockChartBound hF hc hC hσ X hκ

end Langlands.Archimedean
