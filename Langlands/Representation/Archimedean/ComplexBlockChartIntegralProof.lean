import Langlands.Representation.Archimedean.ComplexBlockLimit
import Mathlib.Analysis.Matrix.LDL

/-!
# Proof of the integrability of the block chart bound

`ComplexBlockChartIntegrableStatement`: under the tail condition, `X ↦ blockChartBound ε X` is
integrable on `M_{k×a}(ℂ)`. The proof integrates the first row: by the matrix determinant lemma and
the LDL decomposition of `S = 1 + X'ᴴ X'` (`X'` the remaining rows), the first row enters through
`∏_l partialSq (x M) (l+1)^{ε_l}` for a fixed matrix `M` with `|det M|^{-2} = det S`, and
`det S` cancels the first row factor of the remaining rows.
-/

noncomputable section

open MeasureTheory Matrix Filter Topology

open scoped Matrix ComplexOrder

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace ComplexBlockChartProof

open ComplexBlockChart ComplexBlockLimit

/-! ## Leading principal submatrices -/

section Leading

variable {a m : ℕ}

/-- The leading principal `m × m` submatrix. -/
abbrev lead (h : m ≤ a) (A : Matrix (Fin a) (Fin a) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  A.submatrix (Fin.castLE h) (Fin.castLE h)

theorem sum_eq_sum_castLE (h : m ≤ a) (g : Fin a → ℂ) (hg : ∀ p : Fin a, m ≤ (p : ℕ) → g p = 0) :
    ∑ p, g p = ∑ p : Fin m, g (Fin.castLE h p) := by
  rw [ComplexBlockChart.sum_castLE h]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs with hp
  · rfl
  · exact hg p (by omega)

theorem lead_mul_mul_conjTranspose (h : m ≤ a) {T : Matrix (Fin a) (Fin a) ℂ}
    (hT : T.IsLowerTriangular) (S : Matrix (Fin a) (Fin a) ℂ) :
    lead h (T * S * Tᴴ) = lead h T * lead h S * (lead h T)ᴴ := by
  have hT0 : ∀ i p : Fin a, (i : ℕ) < p → T i p = 0 := fun i p hip => hT (by
    rw [OrderDual.toDual_lt_toDual]
    exact Fin.lt_def.mpr hip)
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [sum_eq_sum_castLE h _ fun q hq => by
    rw [hT0 (Fin.castLE h j) q (by simp; omega), star_zero, mul_zero]]
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 1
  exact sum_eq_sum_castLE h _ fun p hp => by
    rw [hT0 (Fin.castLE h i) p (by simp; omega), zero_mul]

theorem lead_diagonal (h : m ≤ a) (d : Fin a → ℂ) :
    lead h (Matrix.diagonal d) = Matrix.diagonal (d ∘ Fin.castLE h) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.diagonal_apply, Function.comp_apply,
    (Fin.castLE_injective h).eq_iff]

theorem isLowerTriangular_lead (h : m ≤ a) {T : Matrix (Fin a) (Fin a) ℂ}
    (hT : T.IsLowerTriangular) : (lead h T).IsLowerTriangular := by
  intro i j hij
  rw [OrderDual.toDual_lt_toDual] at hij
  apply hT
  rw [OrderDual.toDual_lt_toDual]
  exact Fin.lt_def.mpr (by have := Fin.lt_def.mp hij; simpa using this)

theorem det_lead_lower (h : m ≤ a) {T : Matrix (Fin a) (Fin a) ℂ} (hT : T.IsLowerTriangular) :
    (lead h T).det = ∏ i : Fin m, T (Fin.castLE h i) (Fin.castLE h i) :=
  Matrix.det_of_isLowerTriangular _ (isLowerTriangular_lead h hT)

theorem det_lead_lower_ne_zero (h : m ≤ a) {T : Matrix (Fin a) (Fin a) ℂ}
    (hT : T.IsLowerTriangular) (hdet : T.det ≠ 0) : (lead h T).det ≠ 0 := by
  rw [det_lead_lower h hT]
  rw [Matrix.det_of_isLowerTriangular T hT] at hdet
  exact Finset.prod_ne_zero_iff.mpr fun i _ => (Finset.prod_ne_zero_iff.mp hdet) _ (Finset.mem_univ _)

theorem vecMul_conjTranspose_castLE (h : m ≤ a) {T : Matrix (Fin a) (Fin a) ℂ}
    (hT : T.IsLowerTriangular) (u : Fin a → ℂ) (i : Fin m) :
    (u ᵥ* Tᴴ) (Fin.castLE h i) = ((u ∘ Fin.castLE h) ᵥ* (lead h T)ᴴ) i := by
  have hT0 : ∀ i p : Fin a, (i : ℕ) < p → T i p = 0 := fun i p hip => hT (by
    rw [OrderDual.toDual_lt_toDual]
    exact Fin.lt_def.mpr hip)
  simp only [Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply, Function.comp_apply,
    Matrix.submatrix_apply]
  exact sum_eq_sum_castLE h _ fun p hp => by
    rw [hT0 (Fin.castLE h i) p (by simp; omega), star_zero, mul_zero]

end Leading

/-! ## The rank-one determinant identity -/

section RankOne

variable {a m : ℕ}

/-- The rank-one Hermitian matrix `uᴴ u` of a row vector `u`. -/
def rankOne (u : Fin m → ℂ) : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i j => star (u i) * u j

theorem rankOne_apply (u : Fin m → ℂ) (i j : Fin m) : rankOne u i j = star (u i) * u j := rfl

theorem rankOne_eq (u : Fin m → ℂ) :
    rankOne u = Matrix.replicateCol Unit (star u) * Matrix.replicateRow Unit u := by
  ext i j
  simp [rankOne, Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply]

theorem mul_rankOne_mul (A : Matrix (Fin m) (Fin m) ℂ) (u : Fin m → ℂ) :
    A * rankOne u * Aᴴ = rankOne (u ᵥ* Aᴴ) := by
  ext i j
  simp only [Matrix.mul_apply, rankOne_apply, Matrix.conjTranspose_apply, Matrix.vecMul,
    dotProduct, star_sum, star_mul', star_star, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

theorem det_diagonal_add_rankOne {d : Fin m → ℂ} (hd : ∀ i, d i ≠ 0) (v : Fin m → ℂ) :
    (Matrix.diagonal d + rankOne v).det =
      (Matrix.diagonal d).det * (1 + ∑ i, v i * (d i)⁻¹ * star (v i)) := by
  have hdet : IsUnit (Matrix.diagonal d).det := by
    rw [Matrix.det_diagonal]
    exact (Finset.prod_ne_zero_iff.mpr fun i _ => hd i).isUnit
  have hinv : (Matrix.diagonal d)⁻¹ = Matrix.diagonal (fun i => (d i)⁻¹) := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.diagonal_mul_diagonal]
    have : (fun i => (d i)⁻¹ * d i) = fun _ => (1 : ℂ) := funext fun i => inv_mul_cancel₀ (hd i)
    rw [this, Matrix.diagonal_one]
  rw [rankOne_eq, Matrix.det_add_replicateCol_mul_replicateRow hdet]
  congr 1
  rw [Matrix.det_unique, hinv]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, Matrix.replicateRow_apply,
    Matrix.replicateCol_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Pi.star_apply]

/-- **The rank-one determinant identity.** If `T` is lower triangular and invertible with
`T S Tᴴ = diag(d)`, then for every leading block and row vector `u`,
`det(S_m + u_mᴴ u_m) = det S_m · (1 + ∑_{i<m} |(u Tᴴ)_i|² / d_i)`. -/
theorem det_lead_add_rankOne (h : m ≤ a) {S T : Matrix (Fin a) (Fin a) ℂ} {d : Fin a → ℂ}
    (hT : T.IsLowerTriangular) (hdetT : T.det ≠ 0) (hTS : T * S * Tᴴ = Matrix.diagonal d)
    (hd : ∀ i, d i ≠ 0) (u : Fin a → ℂ) :
    (lead h S + rankOne (u ∘ Fin.castLE h)).det =
      (lead h S).det * (1 + ∑ i : Fin m, (u ᵥ* Tᴴ) (Fin.castLE h i) *
        (d (Fin.castLE h i))⁻¹ * star ((u ᵥ* Tᴴ) (Fin.castLE h i))) := by
  set Tm := lead h T
  have hTm : Tm * lead h S * Tmᴴ = Matrix.diagonal (d ∘ Fin.castLE h) := by
    rw [← lead_mul_mul_conjTranspose h hT, hTS, lead_diagonal]
  have hdm : ∀ i : Fin m, (d ∘ Fin.castLE h) i ≠ 0 := fun i => hd _
  have hv : (u ∘ Fin.castLE h) ᵥ* Tmᴴ = fun i => (u ᵥ* Tᴴ) (Fin.castLE h i) :=
    funext fun i => (vecMul_conjTranspose_castLE h hT u i).symm
  have h1 : Tm * (lead h S + rankOne (u ∘ Fin.castLE h)) * Tmᴴ =
      Matrix.diagonal (d ∘ Fin.castLE h) + rankOne (fun i => (u ᵥ* Tᴴ) (Fin.castLE h i)) := by
    rw [Matrix.mul_add, Matrix.add_mul, hTm, mul_rankOne_mul, hv]
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_mul, det_diagonal_add_rankOne hdm] at h2
  have h3 := congrArg Matrix.det hTm
  rw [Matrix.det_mul, Matrix.det_mul] at h3
  rw [← h3] at h2
  have hTm0 : Tm.det ≠ 0 := det_lead_lower_ne_zero h hT hdetT
  have hTmH0 : Tmᴴ.det ≠ 0 := by
    rw [Matrix.det_conjTranspose]
    exact star_ne_zero.mpr hTm0
  have h4 : Tm.det * Tmᴴ.det ≠ 0 := mul_ne_zero hTm0 hTmH0
  have h5 : (Tm.det * Tmᴴ.det) * (lead h S + rankOne (u ∘ Fin.castLE h)).det =
      (Tm.det * Tmᴴ.det) * ((lead h S).det * (1 + ∑ i : Fin m, (u ᵥ* Tᴴ) (Fin.castLE h i) *
        (d (Fin.castLE h i))⁻¹ * star ((u ᵥ* Tᴴ) (Fin.castLE h i)))) := by
    calc (Tm.det * Tmᴴ.det) * (lead h S + rankOne (u ∘ Fin.castLE h)).det =
          Tm.det * (lead h S + rankOne (u ∘ Fin.castLE h)).det * Tmᴴ.det := by ring
      _ = _ := h2
      _ = _ := by simp only [Function.comp_apply]; ring
  exact mul_left_cancel₀ h4 h5

end RankOne

/-! ## The first row -/

section Cons

variable {a k : ℕ}

theorem sum_castLE_real {l : ℕ} (hl : l ≤ a) (g : Fin a → ℝ) :
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

theorem det_posDef_eq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    A.det = ((A.det).re : ℂ) ∧ 0 < (A.det).re := by
  have h := hA.1.det_eq_prod_eigenvalues
  have h2 : A.det = ((∏ i, hA.1.eigenvalues i : ℝ) : ℂ) := by
    rw [h, Complex.ofReal_prod]
    rfl
  rw [h2, Complex.ofReal_re]
  exact ⟨rfl, Finset.prod_pos fun i _ => hA.eigenvalues_pos i⟩

/-- `S = 1 + X'ᴴ X'`. -/
def gramS (X' : Fin k → Fin a → ℂ) : Matrix (Fin a) (Fin a) ℂ :=
  1 + (Matrix.of X')ᴴ * Matrix.of X'

theorem posDef_gramS (X' : Fin k → Fin a → ℂ) : (gramS X').PosDef :=
  Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self _)

theorem le_of_fin (l : Fin a) : (l : ℕ) + 1 ≤ a := l.isLt

theorem lead_gramS (X' : Fin k → Fin a → ℂ) (l : Fin a) :
    lead (le_of_fin l) (gramS X') =
      1 + (colsUpTo (Matrix.of X') l)ᴴ * colsUpTo (Matrix.of X') l := by
  ext i j
  simp only [gramS, Matrix.submatrix_apply, Matrix.add_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, colsUpTo, Matrix.one_apply, (Fin.castLE_injective _).eq_iff, id]

theorem colsUpTo_cons (x : Fin a → ℂ) (X' : Fin k → Fin a → ℂ) (l : Fin a) :
    1 + (colsUpTo (Matrix.of (Fin.cons x X' : Fin (k + 1) → Fin a → ℂ)) l)ᴴ *
        colsUpTo (Matrix.of (Fin.cons x X' : Fin (k + 1) → Fin a → ℂ)) l =
      lead (le_of_fin l) (gramS X') + rankOne (x ∘ Fin.castLE (le_of_fin l)) := by
  ext i j
  simp only [gramS, Matrix.submatrix_apply, Matrix.add_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, colsUpTo, Matrix.one_apply, (Fin.castLE_injective _).eq_iff, id,
    rankOne_apply, Function.comp_apply, Matrix.of_apply, Fin.sum_univ_succ, Fin.cons_zero,
    Fin.cons_succ]
  ring

/-- The LDL data of `S = 1 + X'ᴴ X'`. -/
abbrev lowT (X' : Fin k → Fin a → ℂ) : Matrix (Fin a) (Fin a) ℂ := LDL.lowerInv (posDef_gramS X')

abbrev diagD (X' : Fin k → Fin a → ℂ) : Fin a → ℂ := LDL.diagEntries (posDef_gramS X')

theorem lowT_conj (X' : Fin k → Fin a → ℂ) :
    lowT X' * gramS X' * (lowT X')ᴴ = Matrix.diagonal (diagD X') :=
  (LDL.diag_eq_lowerInv_conj (posDef_gramS X')).symm

theorem isLowerTriangular_lowT (X' : Fin k → Fin a → ℂ) : (lowT X').IsLowerTriangular :=
  LDL.isLowerTriangular_lowerInv _

theorem det_lowT_ne_zero (X' : Fin k → Fin a → ℂ) : (lowT X').det ≠ 0 :=
  (Matrix.isUnit_det_of_invertible (lowT X')).ne_zero

theorem diagD_pos (X' : Fin k → Fin a → ℂ) (i : Fin a) :
    0 < (diagD X' i).re ∧ (diagD X' i).im = 0 := by
  have hD : (Matrix.diagonal (diagD X')).PosDef := by
    rw [← lowT_conj]
    exact (posDef_gramS X').mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_iff_isUnit.mpr (isUnit_of_invertible (lowT X')))
  have h := hD.diag_pos (i := i)
  rw [Matrix.diagonal_apply_eq, Complex.lt_def] at h
  exact ⟨h.1, h.2.symm⟩

theorem diagD_eq (X' : Fin k → Fin a → ℂ) (i : Fin a) : diagD X' i = ((diagD X' i).re : ℂ) :=
  Complex.ext rfl (by simp [(diagD_pos X' i).2])

/-- `M = Tᴴ diag(d)^{-1/2}`. -/
def matM (X' : Fin k → Fin a → ℂ) : Matrix (Fin a) (Fin a) ℂ :=
  (lowT X')ᴴ * Matrix.diagonal fun i => (((Real.sqrt (diagD X' i).re)⁻¹ : ℝ) : ℂ)

theorem norm_vecMul_matM_sq (X' : Fin k → Fin a → ℂ) (x : Fin a → ℂ) (i : Fin a) :
    ‖(x ᵥ* matM X') i‖ ^ 2 = ‖(x ᵥ* (lowT X')ᴴ) i‖ ^ 2 / (diagD X' i).re := by
  rw [matM, ← Matrix.vecMul_vecMul, Matrix.vecMul_diagonal, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), inv_pow,
    Real.sq_sqrt (diagD_pos X' i).1.le, div_eq_mul_inv]

theorem term_eq (v d : ℂ) (hd : d = (d.re : ℂ)) :
    v * d⁻¹ * star v = ((‖v‖ ^ 2 / d.re : ℝ) : ℂ) := by
  calc v * d⁻¹ * star v = (v * star v) * d⁻¹ := by ring
    _ = ((‖v‖ ^ 2 : ℝ) : ℂ) * ((d.re : ℝ) : ℂ)⁻¹ := by
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← hd]
    _ = _ := by push_cast; ring

/-- **The first row in the column Gram determinants.** -/
theorem colGram_cons (x : Fin a → ℂ) (X' : Fin k → Fin a → ℂ) (l : Fin a) :
    colGram (Matrix.of (Fin.cons x X' : Fin (k + 1) → Fin a → ℂ)) l =
      colGram (Matrix.of X') l *
        ComplexParabolicChartBound.partialSq (x ᵥ* matM X') ((l : ℕ) + 1) := by
  have hd0 : ∀ i, diagD X' i ≠ 0 := fun i h => by
    have := (diagD_pos X' i).1
    rw [h, Complex.zero_re] at this
    exact lt_irrefl _ this
  rw [colGram, colsUpTo_cons, det_lead_add_rankOne (le_of_fin l) (isLowerTriangular_lowT X')
    (det_lowT_ne_zero X') (lowT_conj X') hd0 x, colGram, ← lead_gramS]
  obtain ⟨hR, -⟩ := det_posDef_eq ((posDef_gramS X').submatrix (Fin.castLE_injective (le_of_fin l)))
  have hsum : ∑ i : Fin ((l : ℕ) + 1), (x ᵥ* (lowT X')ᴴ) (Fin.castLE (le_of_fin l) i) *
      (diagD X' (Fin.castLE (le_of_fin l) i))⁻¹ * star ((x ᵥ* (lowT X')ᴴ) (Fin.castLE (le_of_fin l) i)) =
      ((∑ i : Fin ((l : ℕ) + 1), ‖(x ᵥ* matM X') (Fin.castLE (le_of_fin l) i)‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_vecMul_matM_sq]
    exact term_eq _ _ (diagD_eq X' _)
  rw [hsum, hR, ← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_mul,
    Complex.ofReal_re, Complex.ofReal_re]
  congr 1
  rw [ComplexParabolicChartBound.partialSq, sum_castLE_real (le_of_fin l)
    (fun j => ‖(x ᵥ* matM X') j‖ ^ 2)]

end Cons

/-! ## Rows and the factorization of the block chart bound -/

section Rows

variable {a k : ℕ}

theorem rowGram_cons_succ (x : Fin a → ℂ) (X' : Fin k → Fin a → ℂ) (j : Fin k) :
    rowGram (Matrix.of (Fin.cons x X' : Fin (k + 1) → Fin a → ℂ)) j.succ =
      rowGram (Matrix.of X') j := by
  set e : Fin (k + 1 - ((j.succ : Fin (k + 1)) : ℕ)) ≃ Fin (k - (j : ℕ)) :=
    finCongr (by simp) with he
  unfold rowGram
  congr 1
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 1
  ext i i'
  have hidx : ∀ q : Fin (k + 1 - ((j.succ : Fin (k + 1)) : ℕ)),
      (⟨((j.succ : Fin (k + 1)) : ℕ) + q, by omega⟩ : Fin (k + 1)) =
        Fin.succ ⟨(j : ℕ) + (e q : ℕ), by have := (e q).isLt; omega⟩ :=
    fun q => Fin.ext (by simp [he]; omega)
  simp only [Matrix.add_apply, Matrix.submatrix_apply, Matrix.mul_apply, rowsFrom,
    Matrix.conjTranspose_apply, Matrix.of_apply, id, hidx, Fin.cons_succ, Matrix.one_apply,
    e.injective.eq_iff]

theorem rowGram_zero (X' : Fin (k + 1) → Fin a → ℂ) :
    rowGram (Matrix.of X') 0 = (gramS X').det.re := by
  set e : Fin (k + 1 - ((0 : Fin (k + 1)) : ℕ)) ≃ Fin (k + 1) := finCongr (by simp) with he
  unfold rowGram gramS
  congr 1
  rw [Matrix.det_one_add_mul_comm ((Matrix.of X')ᴴ) (Matrix.of X'),
    ← Matrix.det_submatrix_equiv_self e (1 + Matrix.of X' * (Matrix.of X')ᴴ)]
  congr 1
  ext i i'
  have hidx : ∀ q : Fin (k + 1 - ((0 : Fin (k + 1)) : ℕ)),
      (⟨((0 : Fin (k + 1)) : ℕ) + q, by omega⟩ : Fin (k + 1)) = e q :=
    fun q => Fin.ext (by simp [he])
  simp only [Matrix.add_apply, Matrix.submatrix_apply, Matrix.mul_apply, rowsFrom,
    Matrix.conjTranspose_apply, Matrix.of_apply, id, hidx, Matrix.one_apply, e.injective.eq_iff]

theorem gramS_zero (X' : Fin 0 → Fin a → ℂ) : (gramS X').det.re = 1 := by
  have : gramS X' = 1 := by
    ext i j
    simp [gramS]
  rw [this, Matrix.det_one, Complex.one_re]

/-- The row factor of `blockChartBound`. -/
def rowPart (X : Matrix (Fin k) (Fin a) ℂ) : ℝ :=
  ∏ j : Fin k, if (j : ℕ) = 0 then 1 else (rowGram X j)⁻¹

theorem rowPart_cons (x : Fin a → ℂ) (X' : Fin k → Fin a → ℂ) :
    rowPart (Matrix.of (Fin.cons x X' : Fin (k + 1) → Fin a → ℂ)) =
      ((gramS X').det.re)⁻¹ * rowPart (Matrix.of X') := by
  rw [rowPart, Fin.prod_univ_succ]
  simp only [Fin.val_zero, ite_true, one_mul, Fin.val_succ, Nat.succ_ne_zero, ite_false,
    rowGram_cons_succ]
  cases k with
  | zero => simp [rowPart, gramS_zero]
  | succ k' =>
    rw [Fin.prod_univ_succ, rowPart, Fin.prod_univ_succ, rowGram_zero]
    simp only [Fin.val_zero, ite_true, one_mul, Fin.val_succ, Nat.succ_ne_zero, ite_false]

theorem blockChartBound_eq (ε : Fin a → ℝ) (X : Matrix (Fin k) (Fin a) ℂ) :
    blockChartBound ε X = (∏ l, colGram X l ^ ε l) * rowPart X := rfl

theorem partialSq_nonneg {n : ℕ} (y : Fin n → ℂ) (l : ℕ) :
    0 ≤ ComplexParabolicChartBound.partialSq y l := by
  unfold ComplexParabolicChartBound.partialSq
  have : 0 ≤ ∑ j : Fin n, (if (j : ℕ) < l then ‖y j‖ ^ 2 else 0) :=
    Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  linarith

/-- **Factorization.** -/
theorem blockChartBound_cons (ε : Fin a → ℝ) (x : Fin a → ℂ) (X' : Fin k → Fin a → ℂ) :
    blockChartBound ε (Matrix.of (Fin.cons x X' : Fin (k + 1) → Fin a → ℂ)) =
      blockChartBound ε (Matrix.of X') * ((gramS X').det.re)⁻¹ *
        ∏ l : Fin a, ComplexParabolicChartBound.partialSq (x ᵥ* matM X') ((l : ℕ) + 1) ^ ε l := by
  rw [blockChartBound_eq, blockChartBound_eq, rowPart_cons]
  simp only [colGram_cons]
  rw [Finset.prod_congr rfl fun l _ => Real.mul_rpow
    (le_trans zero_le_one (one_le_colGram _ l)) (partialSq_nonneg _ _), Finset.prod_mul_distrib]
  ring

theorem inv_norm_det_matM_sq (X' : Fin k → Fin a → ℂ) :
    (‖(matM X').det‖ ^ 2)⁻¹ = (gramS X').det.re := by
  have hS := det_posDef_eq (posDef_gramS X')
  have hD := congrArg Matrix.det (lowT_conj X')
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_conjTranspose] at hD
  have hprod : ∏ i, diagD X' i = ((∏ i, (diagD X' i).re : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun i _ => diagD_eq X' i
  rw [hprod, hS.1, mul_comm ((lowT X').det), mul_assoc, Complex.star_def, Complex.mul_conj,
    ← Complex.ofReal_mul] at hD
  have hD' := Complex.ofReal_injective hD
  have hT := det_lowT_ne_zero X'
  rw [matM, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_diagonal, norm_mul, norm_star,
    mul_pow, ← Complex.ofReal_prod, Complex.norm_real, Real.norm_of_nonneg (Finset.prod_nonneg
      fun i _ => inv_nonneg.mpr (Real.sqrt_nonneg _)), ← Finset.prod_pow]
  have hsq : ∀ i, ((Real.sqrt (diagD X' i).re)⁻¹) ^ 2 = ((diagD X' i).re)⁻¹ := fun i => by
    rw [inv_pow, Real.sq_sqrt (diagD_pos X' i).1.le]
  simp only [hsq]
  rw [Finset.prod_inv_distrib]
  rw [Complex.normSq_eq_norm_sq] at hD'
  have hpos : 0 < ∏ i, (diagD X' i).re := Finset.prod_pos fun i _ => (diagD_pos X' i).1
  have hTn : 0 < ‖(lowT X').det‖ ^ 2 := pow_pos (norm_pos_iff.mpr hT) 2
  rw [← hD']
  field_simp

end Rows

/-! ## Integration over the first row and the induction -/

section Integral

variable {a k : ℕ} {ε : Fin a → ℝ}

theorem continuous_colGram (l : Fin a) :
    Continuous fun X : Fin k → Fin a → ℂ => colGram (Matrix.of X) l := by
  have hsub : Continuous fun X : Fin k → Fin a → ℂ => colsUpTo (Matrix.of X) l :=
    continuous_id.matrix_submatrix _ _
  exact Complex.continuous_re.comp (Continuous.matrix_det (continuous_const.add
    (hsub.matrix_conjTranspose.matrix_mul hsub)))

theorem continuous_rowGram (j : Fin k) :
    Continuous fun X : Fin k → Fin a → ℂ => rowGram (Matrix.of X) j := by
  have hsub : Continuous fun X : Fin k → Fin a → ℂ => rowsFrom (Matrix.of X) j :=
    continuous_id.matrix_submatrix _ _
  exact Complex.continuous_re.comp (Continuous.matrix_det (continuous_const.add
    (hsub.matrix_mul hsub.matrix_conjTranspose)))

theorem continuous_blockChartBound (ε : Fin a → ℝ) :
    Continuous fun X : Fin k → Fin a → ℂ => blockChartBound ε (Matrix.of X) := by
  unfold blockChartBound
  refine Continuous.mul (continuous_finsetProd _ fun l _ => ?_)
    (continuous_finsetProd _ fun j _ => ?_)
  · exact (continuous_colGram l).rpow_const fun X =>
      Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_colGram _ l)))
  · by_cases hj : (j : ℕ) = 0
    · simp only [hj, ite_true]
      exact continuous_const
    · simp only [hj, ite_false]
      exact (continuous_rowGram j).inv₀ fun X =>
        ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_rowGram _ j))

/-- `C_ε = ∫_{ℂ^a} ∏_l partialSq y (l+1)^{ε_l} dy`. -/
def constC (ε : Fin a → ℝ) : ℝ :=
  ∫ y : Fin a → ℂ, ∏ l : Fin a, ComplexParabolicChartBound.partialSq y ((l : ℕ) + 1) ^ ε l

theorem prod_partialSq_nonneg (ε : Fin a → ℝ) (y : Fin a → ℂ) :
    0 ≤ ∏ l : Fin a, ComplexParabolicChartBound.partialSq y ((l : ℕ) + 1) ^ ε l :=
  Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (partialSq_nonneg _ _) _

theorem det_matM_ne_zero (X' : Fin k → Fin a → ℂ) : (matM X').det ≠ 0 := by
  intro h
  have h1 := inv_norm_det_matM_sq X'
  rw [h, norm_zero, zero_pow two_ne_zero, _root_.inv_zero] at h1
  exact (ne_of_gt (det_posDef_eq (posDef_gramS X')).2) h1.symm

theorem lintegral_first_row (hε : ComplexPartialSqIntegral.TailCondition ε 0)
    (X' : Fin k → Fin a → ℂ) :
    ∫⁻ x : Fin a → ℂ, ENNReal.ofReal (∏ l : Fin a,
      ComplexParabolicChartBound.partialSq (x ᵥ* matM X') ((l : ℕ) + 1) ^ ε l) =
      ENNReal.ofReal ((gramS X').det.re) * ENNReal.ofReal (constC ε) := by
  have hdet := det_matM_ne_zero X'
  set f : (Fin a → ℂ) → ENNReal := fun y => ENNReal.ofReal (∏ l : Fin a,
    ComplexParabolicChartBound.partialSq y ((l : ℕ) + 1) ^ ε l) with hf
  have h1 : (∫⁻ x : Fin a → ℂ, ENNReal.ofReal (∏ l : Fin a,
      ComplexParabolicChartBound.partialSq (x ᵥ* matM X') ((l : ℕ) + 1) ^ ε l)) =
      ∫⁻ x, f (ComplexPartialJacquet.vecMulEquiv hdet x) := rfl
  rw [h1, ← lintegral_map_equiv f (ComplexPartialJacquet.vecMulEquiv hdet),
    ComplexPartialJacquet.map_vecMulEquiv, lintegral_smul_measure, inv_norm_det_matM_sq]
  congr 1
  rw [constC, ofReal_integral_eq_lintegral_ofReal
    (ComplexPartialSqIntegral.integrable_prod_partialSq hε)
    (ae_of_all _ fun y => prod_partialSq_nonneg ε y)]

theorem lintegral_cons (hε : ComplexPartialSqIntegral.TailCondition ε 0)
    (X' : Fin k → Fin a → ℂ) :
    ∫⁻ x : Fin a → ℂ, ENNReal.ofReal
      (blockChartBound ε (Matrix.of (Fin.cons x X' : Fin (k + 1) → Fin a → ℂ))) =
      ENNReal.ofReal (blockChartBound ε (Matrix.of X')) * ENNReal.ofReal (constC ε) := by
  have hS := (det_posDef_eq (posDef_gramS X')).2
  have hB := ComplexBlockLimit.blockChartBound_nonneg ε (Matrix.of X')
  have hA : 0 ≤ blockChartBound ε (Matrix.of X') * ((gramS X').det.re)⁻¹ :=
    mul_nonneg hB (inv_nonneg.mpr hS.le)
  simp only [blockChartBound_cons, ENNReal.ofReal_mul hA]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_first_row hε, ← mul_assoc,
    ← ENNReal.ofReal_mul hA, mul_assoc, inv_mul_cancel₀ hS.ne', mul_one]

theorem lintegral_eq_cons (F : (Fin (k + 1) → Fin a → ℂ) → ENNReal) (hF : Measurable F) :
    ∫⁻ X, F X = ∫⁻ X' : Fin k → Fin a → ℂ, ∫⁻ x : Fin a → ℂ, F (Fin.cons x X') := by
  have hmp := measurePreserving_piFinSuccAbove
    (fun _ : Fin (k + 1) => (volume : Measure (Fin a → ℂ))) 0
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => Fin a → ℂ) 0 with he
  rw [volume_pi, ← hmp.symm.lintegral_comp_emb e.symm.measurableEmbedding F,
    lintegral_prod_symm' (fun p => F (e.symm p)) (hF.comp e.symm.measurable)]
  have hcons : ∀ (x : Fin a → ℂ) (X' : Fin k → Fin a → ℂ), e.symm (x, X') = Fin.cons x X' := by
    intro x X'
    funext j
    refine Fin.cases ?_ (fun j' => ?_) j
    · simp [he, MeasurableEquiv.piFinSuccAbove]
    · simp [he, MeasurableEquiv.piFinSuccAbove]
  simp only [hcons]
  rfl

theorem blockChartBound_zero_rows (ε : Fin a → ℝ) (X : Fin 0 → Fin a → ℂ) :
    blockChartBound ε (Matrix.of X) = 1 := by
  have hcol : ∀ l : Fin a, colGram (Matrix.of X) l = 1 := fun l => by
    have : (colsUpTo (Matrix.of X) l)ᴴ * colsUpTo (Matrix.of X) l = 0 := by
      ext i j
      simp [Matrix.mul_apply]
    rw [colGram, this, add_zero, Matrix.det_one, Complex.one_re]
  simp [blockChartBound, hcol]

theorem integrable_rows (hε : ComplexPartialSqIntegral.TailCondition ε 0) :
    ∀ k : ℕ, Integrable fun X : Fin k → Fin a → ℂ => blockChartBound ε (Matrix.of X)
  | 0 => by
    have : IsFiniteMeasure (volume : Measure (Fin 0 → Fin a → ℂ)) :=
      ⟨by rw [volume_pi, Measure.pi_univ]; simp⟩
    simp only [blockChartBound_zero_rows]
    exact integrable_const 1
  | k + 1 => by
    have IH := integrable_rows hε k
    refine ⟨(continuous_blockChartBound ε).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun X =>
      ComplexBlockLimit.blockChartBound_nonneg ε _),
      lintegral_eq_cons (fun X => ENNReal.ofReal (blockChartBound ε (Matrix.of X)))
        (ENNReal.measurable_ofReal.comp (continuous_blockChartBound ε).measurable)]
    simp only [lintegral_cons hε]
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ((hasFiniteIntegral_iff_ofReal (ae_of_all _ fun X =>
      ComplexBlockLimit.blockChartBound_nonneg ε _)).mp IH.2) ENNReal.ofReal_lt_top

end Integral

end ComplexBlockChartProof

/-- **Statement (integration of the first row).** For all `a, k`, `ε : Fin a → ℝ` with
`∑_{l ≥ j} (ε_l + 1) < 0` for every `j < a`, and every `X' ∈ M_{k×a}(ℂ)`,
`∫_{ℂ^a} blockChartBound ε [x; X'] dx = blockChartBound ε X' · C_ε` (as extended nonnegative
reals), where `[x; X']` is the matrix with first row `x` and remaining rows `X'`, and
`C_ε = ∫_{ℂ^a} ∏_l (1 + ∑_{i ≤ l} |y_i|²)^{ε_l} dy`. -/
def ComplexBlockChartFirstRowStatement : Prop :=
  ∀ (a k : ℕ) (ε : Fin a → ℝ),
    (∀ j : Fin a, ∑ l : Fin a, (if j ≤ l then ε l + 1 else 0) < 0) →
    ∀ X' : Fin k → Fin a → ℂ,
      ∫⁻ x : Fin a → ℂ, ENNReal.ofReal (ComplexBlockChart.blockChartBound ε
          (Matrix.of (Fin.cons x X' : Fin (k + 1) → Fin a → ℂ))) =
        ENNReal.ofReal (ComplexBlockChart.blockChartBound ε (Matrix.of X')) *
          ENNReal.ofReal (∫ y : Fin a → ℂ, ∏ l : Fin a,
            ComplexParabolicChartBound.partialSq y ((l : ℕ) + 1) ^ ε l)

theorem complexBlockChartFirstRow : ComplexBlockChartFirstRowStatement := by
  intro a k ε hε X'
  exact ComplexBlockChartProof.lintegral_cons (fun j => by rw [zero_add]; exact hε j) X'

/-- **Proof of `ComplexBlockChartIntegrableStatement`.** -/
theorem complexBlockChartIntegrable : ComplexBlockChartIntegrableStatement := by
  intro a k ε hε
  exact ComplexBlockChartProof.integrable_rows (ε := ε)
    (fun j => by rw [zero_add]; exact hε j) k

end Langlands.Archimedean
