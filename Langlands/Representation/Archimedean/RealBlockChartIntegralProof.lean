import Langlands.Representation.Archimedean.RealBlockLimit
import Langlands.Representation.Archimedean.PartialSqIntegral
import Langlands.Representation.Archimedean.PartialJacquetIntegral
import Langlands.Representation.Archimedean.RealBlockChartBound
import Mathlib.Analysis.Matrix.LDL

/-!
# Integrability of the real block chart bound

A normalized lower triangular factor of the Gram matrix of the remaining rows
reduces integration of the first row to a product of powers of partial square
sums. Its change-of-variables factor cancels the first remaining row determinant.
-/

noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ENNReal Matrix

namespace Langlands.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RealBlockChartProof

open RealBlockChart ParabolicChartBound

variable {a k : ℕ}

private theorem partialSq_mono (y : Fin a → ℝ) : Monotone (partialSq y) := by
  intro m n hmn
  unfold partialSq
  gcongr with i
  by_cases hi : (i : ℕ) < m
  · simp [hi, lt_of_lt_of_le hi hmn]
  · simp only [hi, ite_false]
    split_ifs <;> positivity

private def partialProduct (ε : Fin a → ℝ) (y : Fin a → ℝ) : ℝ :=
  ∏ l : Fin a, partialSq y ((l : ℕ) + 1) ^ ε l

private theorem partialProduct_nonneg (ε : Fin a → ℝ) (y : Fin a → ℝ) :
    0 ≤ partialProduct ε y :=
  Finset.prod_nonneg fun l _ => (Real.rpow_pos_of_pos (partialSq_pos y ((l : ℕ) + 1)) (ε l)).le

private theorem continuous_partialProduct (ε : Fin a → ℝ) : Continuous (partialProduct ε) :=
  continuous_finsetProd _ fun l _ => (PartialSqIntegral.continuous_partialSq ((l : ℕ) + 1)).rpow_const fun y =>
    Or.inl (partialSq_pos y _).ne'

/-- A single exponent strictly below `-1/2` dominates all the tail sums. -/
private theorem exists_comparison_exponent (ε : Fin a → ℝ)
    (hε : ∀ j : Fin a, ∑ l : Fin a, (if j ≤ l then ε l + 1 / 2 else 0) < 0) :
    ∃ b < -(1 / 2 : ℝ), ∀ j : Fin a, ∑ l : Fin a, (if j ≤ l then ε l - b else 0) ≤ 0 := by
  let g (j : Fin a) (b : ℝ) := ∑ l : Fin a, if j ≤ l then ε l - b else 0
  have hcont (j : Fin a) : Continuous (g j) := by
    refine continuous_finsetSum _ fun l _ => ?_
    split_ifs
    · exact continuous_const.sub continuous_id
    · exact continuous_const
  have h : ∀ᶠ b in 𝓝 (-(1 / 2 : ℝ)), ∀ j : Fin a, g j b < 0 :=
    Filter.eventually_all.mpr fun j => (hcont j).continuousAt.eventually_lt continuousAt_const
      (by simpa [g, sub_neg_eq_add] using hε j)
  have hlt : ∀ᶠ b in 𝓝[<] (-(1 / 2 : ℝ)), b < -(1 / 2 : ℝ) := self_mem_nhdsWithin
  obtain ⟨b, hb, htail⟩ := (hlt.and (h.filter_mono nhdsWithin_le_nhds)).exists
  exact ⟨b, hb, fun j => (htail j).le⟩

/-- Summation by parts against a nonnegative increasing sequence. -/
private theorem sum_mul_nonpos_of_tail : ∀ {n : ℕ} (f d : Fin n → ℝ),
    Monotone f → (∀ i, 0 ≤ f i) → (∀ j, ∑ i, (if j ≤ i then d i else 0) ≤ 0) →
    ∑ i, f i * d i ≤ 0
  | 0, _, _, _, _, _ => by simp
  | n + 1, f, d, hf, hf0, hd => by
    have htotal : ∑ i, d i ≤ 0 := by simpa using hd 0
    have htail := sum_mul_nonpos_of_tail (fun i : Fin n => f i.succ - f 0) (fun i => d i.succ)
      (fun i j hij => sub_le_sub_right (hf (Fin.succ_le_succ_iff.mpr hij)) _)
      (fun i => sub_nonneg.mpr (hf (Fin.zero_le i.succ)))
      (fun j => by simpa [Fin.sum_univ_succ] using hd j.succ)
    calc
      ∑ i, f i * d i = f 0 * (∑ i, d i) + ∑ i : Fin n, (f i.succ - f 0) * d i.succ := by
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ, mul_add, Finset.mul_sum]
        simp_rw [sub_mul]
        rw [Finset.sum_sub_distrib]
        ring
      _ ≤ 0 := add_nonpos (mul_nonpos_of_nonneg_of_nonpos (hf0 0) htotal) htail

private theorem integrable_partialProduct (ε : Fin a → ℝ)
    (hε : ∀ j : Fin a, ∑ l : Fin a, (if j ≤ l then ε l + 1 / 2 else 0) < 0) :
    Integrable (partialProduct ε) := by
  obtain ⟨b, hb, htail⟩ := exists_comparison_exponent ε hε
  have hcomp := integrable_prod_one_add_sq_rpow (γ := fun _ : Fin a => b) (fun _ => by linarith)
  refine hcomp.mono' (continuous_partialProduct ε).aestronglyMeasurable (ae_of_all _ fun y => ?_)
  rw [Real.norm_of_nonneg (partialProduct_nonneg ε y)]
  calc
    partialProduct ε y ≤ partialProduct (fun _ => b) y := by
      unfold partialProduct
      simp_rw [Real.rpow_def_of_pos (partialSq_pos y _), ← Real.exp_sum, Real.exp_le_exp]
      rw [← sub_nonpos, ← Finset.sum_sub_distrib]
      simp_rw [← mul_sub]
      refine sum_mul_nonpos_of_tail _ _ (fun i j hij => ?_)
        (fun i => Real.log_nonneg (one_le_partialSq y _)) htail
      exact (Real.log_le_log_iff (partialSq_pos y _) (partialSq_pos y _)).2
        (partialSq_mono y (Nat.succ_le_succ (Fin.le_def.mp hij)))
    _ ≤ ∏ l : Fin a, (1 + y l ^ 2) ^ b :=
      prod_partialSq_rpow_le (fun _ => by linarith)

/-! ## Triangular normalization of the Gram matrix -/

private theorem gram_posDef (X : Matrix (Fin k) (Fin a) ℝ) :
    (1 + Xᵀ * X).PosDef :=
  Matrix.PosDef.one.add_posSemidef (by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self X)

/-- Rescale the rows of the inverse LDL factor to make the diagonal the identity. -/
private theorem exists_lower_normalization {S : Matrix (Fin a) (Fin a) ℝ} (hS : S.PosDef) :
    ∃ T : Matrix (Fin a) (Fin a) ℝ, T.IsLowerTriangular ∧ T * S * Tᵀ = 1 := by
  let L := LDL.lowerInv hS
  let d := LDL.diagEntries hS
  have hL : L * S * Lᵀ = Matrix.diagonal d := by
    simpa only [LDL.diag, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (LDL.diag_eq_lowerInv_conj hS).symm
  have hD : (Matrix.diagonal d).PosDef := by
    rw [← LDL.diag, LDL.diag_eq_lowerInv_conj]
    exact hS.mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_iff_isUnit.mpr (isUnit_of_invertible (LDL.lowerInv hS)))
  have hd (i : Fin a) : 0 < d i := by
    simpa only [Matrix.diagonal_apply_eq] using hD.diag_pos (i := i)
  let scale : Fin a → ℝ := fun i => (Real.sqrt (d i))⁻¹
  refine ⟨Matrix.diagonal scale * L, ?_, ?_⟩
  · have htri : L.IsLowerTriangular := LDL.isLowerTriangular_lowerInv hS
    intro i j hij
    rw [Matrix.diagonal_mul, htri hij, mul_zero]
  · rw [Matrix.transpose_mul, Matrix.diagonal_transpose]
    calc
      Matrix.diagonal scale * L * S * (Lᵀ * Matrix.diagonal scale) =
          Matrix.diagonal scale * (L * S * Lᵀ) * Matrix.diagonal scale := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hL, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        funext i
        have hs : Real.sqrt (d i) ≠ 0 := (Real.sqrt_pos.2 (hd i)).ne'
        change (Real.sqrt (d i))⁻¹ * d i * (Real.sqrt (d i))⁻¹ = 1
        calc
          _ = (Real.sqrt (d i))⁻¹ * (Real.sqrt (d i)) ^ 2 * (Real.sqrt (d i))⁻¹ := by
            rw [Real.sq_sqrt (hd i).le]
          _ = 1 := by field_simp

private abbrev lead {m : ℕ} (h : m ≤ a) (A : Matrix (Fin a) (Fin a) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  A.submatrix (Fin.castLE h) (Fin.castLE h)

private theorem sum_eq_sum_castLE {m : ℕ} (h : m ≤ a) (g : Fin a → ℝ)
    (hg : ∀ p : Fin a, m ≤ (p : ℕ) → g p = 0) :
    ∑ p, g p = ∑ p : Fin m, g (Fin.castLE h p) := by
  rw [RealBlockChart.sum_castLE h]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs with hp
  · rfl
  · exact hg p (Nat.le_of_not_gt hp)

private theorem lower_entry_zero {T : Matrix (Fin a) (Fin a) ℝ} (hT : T.IsLowerTriangular)
    {i p : Fin a} (h : (i : ℕ) < (p : ℕ)) : T i p = 0 := by
  apply hT
  rw [OrderDual.toDual_lt_toDual]
  exact Fin.lt_def.mpr h

private theorem lead_mul_mul_transpose {m : ℕ} (h : m ≤ a)
    {T : Matrix (Fin a) (Fin a) ℝ} (hT : T.IsLowerTriangular) (S : Matrix (Fin a) (Fin a) ℝ) :
    lead h (T * S * Tᵀ) = lead h T * lead h S * (lead h T)ᵀ := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [sum_eq_sum_castLE h _ fun q hq => by
    rw [lower_entry_zero hT (i := Fin.castLE h j) (p := q) (by simp; omega), mul_zero]]
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 1
  exact sum_eq_sum_castLE h _ fun p hp => by
    rw [lower_entry_zero hT (i := Fin.castLE h i) (p := p) (by simp; omega), zero_mul]

private theorem vecMul_transpose_castLE {m : ℕ} (h : m ≤ a)
    {T : Matrix (Fin a) (Fin a) ℝ} (hT : T.IsLowerTriangular) (x : Fin a → ℝ) :
    (x ∘ Fin.castLE h) ᵥ* (lead h T)ᵀ = (x ᵥ* Tᵀ) ∘ Fin.castLE h := by
  funext i
  simp only [Matrix.vecMul, dotProduct, Matrix.transpose_apply, Function.comp_apply,
    Matrix.submatrix_apply]
  symm
  exact sum_eq_sum_castLE h _ fun p hp => by
    rw [lower_entry_zero hT (i := Fin.castLE h i) (p := p) (by simp; omega), mul_zero]

private theorem det_normalization {T S : Matrix (Fin a) (Fin a) ℝ}
    (hTS : T * S * Tᵀ = 1) : T.det ^ 2 * S.det = 1 := by
  simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, pow_two, mul_right_comm]
    using congrArg Matrix.det hTS

/-- Leading Gram determinants after adjoining a row, in normalized coordinates. -/
private theorem det_lead_add_rankOne {m : ℕ} (h : m ≤ a)
    {S T : Matrix (Fin a) (Fin a) ℝ} (hT : T.IsLowerTriangular) (hTS : T * S * Tᵀ = 1)
    (x : Fin a → ℝ) :
    (lead h S + Matrix.vecMulVec (x ∘ Fin.castLE h) (x ∘ Fin.castLE h)).det =
      (lead h S).det * partialSq (x ᵥ* Tᵀ) m := by
  let A := lead h T
  let Q := lead h S
  let v := x ∘ Fin.castLE h
  let z := (x ᵥ* Tᵀ) ∘ Fin.castLE h
  have hAQ : A * Q * Aᵀ = 1 := by
    change lead h T * lead h S * (lead h T)ᵀ = 1
    rw [← lead_mul_mul_transpose h hT, hTS]
    exact Matrix.submatrix_one _ (Fin.castLE_injective h)
  have hz : v ᵥ* Aᵀ = z := vecMul_transpose_castLE h hT x
  have hnorm : A * (Q + Matrix.vecMulVec v v) * Aᵀ = 1 + Matrix.vecMulVec z z := by
    rw [Matrix.mul_add, Matrix.add_mul, hAQ, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
      ← Matrix.vecMul_transpose, hz]
  have hdet := congrArg Matrix.det hnorm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.vecMulVec_eq Unit z z,
    Matrix.det_one_add_replicateCol_mul_replicateRow] at hdet
  have hQ := det_normalization hAQ
  have hA : A.det ^ 2 ≠ 0 := by
    intro h0
    simp [h0] at hQ
  change (Q + Matrix.vecMulVec v v).det = Q.det * partialSq (x ᵥ* Tᵀ) m
  apply mul_left_cancel₀ hA
  rw [← mul_assoc, hQ, one_mul]
  calc
    A.det ^ 2 * (Q + Matrix.vecMulVec v v).det =
        A.det * (Q + Matrix.vecMulVec v v).det * A.det := by ring
    _ = 1 + ∑ i, z i ^ 2 := by simpa only [dotProduct, pow_two] using hdet
    _ = _ := by rw [partialSq, ← RealBlockChart.sum_castLE h]; rfl

private theorem det_transpose_ne_zero {S T : Matrix (Fin a) (Fin a) ℝ}
    (hTS : T * S * Tᵀ = 1) : Tᵀ.det ≠ 0 := by
  rw [Matrix.det_transpose]
  intro h0
  have hd := det_normalization hTS
  simp [h0] at hd

private theorem rpow_det_of_normalization {S T : Matrix (Fin a) (Fin a) ℝ}
    (hTS : T * S * Tᵀ = 1) : |Tᵀ.det⁻¹| = S.det ^ (1 / 2 : ℝ) := by
  have hsq : (T.det⁻¹) ^ 2 = S.det := by
    rw [inv_pow]
    exact (eq_inv_of_mul_eq_one_right (det_normalization hTS)).symm
  rw [Matrix.det_transpose, ← Real.sqrt_sq_eq_abs, hsq, Real.sqrt_eq_rpow]

/-! ## Separating the first row of the bound -/

private def gramS (X' : Fin k → Fin a → ℝ) : Matrix (Fin a) (Fin a) ℝ :=
  1 + (Matrix.of X')ᵀ * Matrix.of X'

private theorem colGram_pos (X : Matrix (Fin k) (Fin a) ℝ) (l : Fin a) :
    0 < colGram X l :=
  (gram_posDef (colsUpTo X l)).det_pos

private theorem rowGram_pos (X : Matrix (Fin k) (Fin a) ℝ) (j : Fin k) :
    0 < rowGram X j := by
  simpa only [rowGram, Matrix.transpose_transpose] using
    (gram_posDef (rowsFrom X j)ᵀ).det_pos

private theorem lead_gramS (X' : Fin k → Fin a → ℝ) (l : Fin a) :
    lead l.isLt (gramS X') = 1 + (colsUpTo (Matrix.of X') l)ᵀ * colsUpTo (Matrix.of X') l := by
  ext i j
  simp only [gramS, Matrix.submatrix_apply, Matrix.add_apply, Matrix.mul_apply,
    Matrix.transpose_apply, colsUpTo, Matrix.one_apply, (Fin.castLE_injective _).eq_iff, id]

private theorem colGram_cons (X' : Fin k → Fin a → ℝ)
    {T : Matrix (Fin a) (Fin a) ℝ} (hT : T.IsLowerTriangular) (hTS : T * gramS X' * Tᵀ = 1)
    (x : Fin a → ℝ) (l : Fin a) :
    colGram (Matrix.of (Fin.cons x X')) l =
      colGram (Matrix.of X') l * partialSq (x ᵥ* Tᵀ) ((l : ℕ) + 1) := by
  let X := colsUpTo (Matrix.of (Fin.cons x X')) l
  let v := x ∘ Fin.castLE l.isLt
  have h : 1 + Xᵀ * X = lead l.isLt (gramS X') + Matrix.vecMulVec v v := by
    ext i j
    simp only [X, v, gramS, Matrix.submatrix_apply, Matrix.add_apply, Matrix.mul_apply,
      Matrix.transpose_apply, colsUpTo, Matrix.one_apply, (Fin.castLE_injective _).eq_iff, id,
      Matrix.vecMulVec_apply, Function.comp_apply, Matrix.of_apply, Fin.sum_univ_succ,
      Fin.cons_zero, Fin.cons_succ]
    ring
  change (1 + Xᵀ * X).det = _
  rw [h, det_lead_add_rankOne l.isLt hT hTS, lead_gramS, colGram]

private theorem rowGram_cons_succ (x : Fin a → ℝ) (X' : Fin k → Fin a → ℝ) (j : Fin k) :
    rowGram (Matrix.of (Fin.cons x X')) j.succ = rowGram (Matrix.of X') j := by
  set e : Fin (k + 1 - (j.succ : ℕ)) ≃ Fin (k - (j : ℕ)) := finCongr (by simp) with he
  unfold rowGram
  rw [← Matrix.det_submatrix_equiv_self e
    (1 + rowsFrom (Matrix.of X') j * (rowsFrom (Matrix.of X') j)ᵀ)]
  congr 1
  ext i i'
  have hidx (q : Fin (k + 1 - (j.succ : ℕ))) :
      (⟨(j.succ : ℕ) + q, by omega⟩ : Fin (k + 1)) =
        Fin.succ ⟨(j : ℕ) + (e q : ℕ), by have := (e q).isLt; omega⟩ :=
    Fin.ext (by simp [he]; omega)
  simp only [Matrix.add_apply, Matrix.submatrix_apply, Matrix.mul_apply, rowsFrom,
    Matrix.transpose_apply, Matrix.of_apply, id, hidx, Fin.cons_succ, Matrix.one_apply,
    e.injective.eq_iff]

private theorem rowGram_zero (X' : Fin (k + 1) → Fin a → ℝ) :
    rowGram (Matrix.of X') 0 = (gramS X').det := by
  set e : Fin (k + 1 - ((0 : Fin (k + 1)) : ℕ)) ≃ Fin (k + 1) := finCongr (by simp) with he
  unfold rowGram gramS
  rw [Matrix.det_one_add_mul_comm ((Matrix.of X')ᵀ) (Matrix.of X'),
    ← Matrix.det_submatrix_equiv_self e (1 + Matrix.of X' * (Matrix.of X')ᵀ)]
  congr 1
  ext i i'
  have hidx (q : Fin (k + 1 - ((0 : Fin (k + 1)) : ℕ))) :
      (⟨((0 : Fin (k + 1)) : ℕ) + q, by omega⟩ : Fin (k + 1)) = e q :=
    Fin.ext (by simp [he])
  simp only [Matrix.add_apply, Matrix.submatrix_apply, Matrix.mul_apply, rowsFrom,
    Matrix.transpose_apply, Matrix.of_apply, id, hidx, Matrix.one_apply, e.injective.eq_iff]

private theorem gramS_zero (X' : Fin 0 → Fin a → ℝ) : (gramS X').det = 1 := by
  have h : gramS X' = 1 := by
    ext i j
    simp [gramS]
  rw [h, Matrix.det_one]

private def rowPart (X : Matrix (Fin k) (Fin a) ℝ) : ℝ :=
  ∏ j : Fin k, if (j : ℕ) = 0 then 1 else rowGram X j ^ (-(1 / 2 : ℝ))

private theorem rowPart_cons (x : Fin a → ℝ) (X' : Fin k → Fin a → ℝ) :
    rowPart (Matrix.of (Fin.cons x X')) =
      (gramS X').det ^ (-(1 / 2 : ℝ)) * rowPart (Matrix.of X') := by
  rw [rowPart, Fin.prod_univ_succ]
  simp only [Fin.val_zero, ite_true, one_mul, Fin.val_succ, Nat.succ_ne_zero, ite_false,
    rowGram_cons_succ]
  cases k with
  | zero => simp [rowPart, gramS_zero]
  | succ k' =>
    rw [Fin.prod_univ_succ, rowPart, Fin.prod_univ_succ, rowGram_zero]
    simp only [Fin.val_zero, ite_true, one_mul, Fin.val_succ, Nat.succ_ne_zero, ite_false]

private theorem blockChartBound_eq (ε : Fin a → ℝ) (X : Matrix (Fin k) (Fin a) ℝ) :
    blockChartBound ε X = (∏ l, colGram X l ^ ε l) * rowPart X := rfl

private theorem blockChartBound_cons (ε : Fin a → ℝ) (X' : Fin k → Fin a → ℝ)
    {T : Matrix (Fin a) (Fin a) ℝ} (hT : T.IsLowerTriangular) (hTS : T * gramS X' * Tᵀ = 1)
    (x : Fin a → ℝ) :
    blockChartBound ε (Matrix.of (Fin.cons x X')) =
      blockChartBound ε (Matrix.of X') * (gramS X').det ^ (-(1 / 2 : ℝ)) *
        partialProduct ε (x ᵥ* Tᵀ) := by
  rw [blockChartBound_eq, blockChartBound_eq, rowPart_cons]
  simp only [colGram_cons X' hT hTS]
  rw [Finset.prod_congr rfl fun l _ => Real.mul_rpow (colGram_pos _ l).le
    (partialSq_pos (x ᵥ* Tᵀ) ((l : ℕ) + 1)).le, Finset.prod_mul_distrib]
  unfold partialProduct
  ring

/-! ## Integrating the first row and inducting over the remaining rows -/

private theorem continuous_colGram (l : Fin a) :
    Continuous fun X : Fin k → Fin a → ℝ => colGram (Matrix.of X) l := by
  have hsub : Continuous fun X : Fin k → Fin a → ℝ => colsUpTo (Matrix.of X) l :=
    continuous_id.matrix_submatrix _ _
  exact Continuous.matrix_det (continuous_const.add (hsub.matrix_transpose.matrix_mul hsub))

private theorem continuous_rowGram (j : Fin k) :
    Continuous fun X : Fin k → Fin a → ℝ => rowGram (Matrix.of X) j := by
  have hsub : Continuous fun X : Fin k → Fin a → ℝ => rowsFrom (Matrix.of X) j :=
    continuous_id.matrix_submatrix _ _
  exact Continuous.matrix_det (continuous_const.add (hsub.matrix_mul hsub.matrix_transpose))

private theorem continuous_blockChartBound (ε : Fin a → ℝ) :
    Continuous fun X : Fin k → Fin a → ℝ => blockChartBound ε (Matrix.of X) := by
  unfold blockChartBound
  refine Continuous.mul (continuous_finsetProd _ fun l _ => ?_)
    (continuous_finsetProd _ fun j _ => ?_)
  · exact (continuous_colGram l).rpow_const fun X => Or.inl (colGram_pos (Matrix.of X) l).ne'
  · split_ifs
    · exact continuous_const
    · exact (continuous_rowGram j).rpow_const fun X => Or.inl (rowGram_pos (Matrix.of X) j).ne'

private def rowIntegral (ε : Fin a → ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (partialProduct ε y)

private theorem lintegral_first_row (ε : Fin a → ℝ) {S T : Matrix (Fin a) (Fin a) ℝ}
    (hTS : T * S * Tᵀ = 1) :
    ∫⁻ x : Fin a → ℝ, ENNReal.ofReal (partialProduct ε (x ᵥ* Tᵀ)) =
      ENNReal.ofReal (S.det ^ (1 / 2 : ℝ)) * rowIntegral ε := by
  let F : (Fin a → ℝ) → ℝ≥0∞ := fun y => ENNReal.ofReal (partialProduct ε y)
  let e := PartialJacquet.vecMulEquiv (det_transpose_ne_zero hTS)
  change ∫⁻ x, F (e x) = _
  rw [← lintegral_map_equiv F e, PartialJacquet.map_vecMulEquiv,
    lintegral_smul_measure, rpow_det_of_normalization hTS]
  rfl

private theorem lintegral_cons (ε : Fin a → ℝ) (X' : Fin k → Fin a → ℝ) :
    ∫⁻ x : Fin a → ℝ, ENNReal.ofReal (blockChartBound ε (Matrix.of (Fin.cons x X'))) =
      ENNReal.ofReal (blockChartBound ε (Matrix.of X')) * rowIntegral ε := by
  have hGram : (gramS X').PosDef := gram_posDef (Matrix.of X')
  obtain ⟨T, hT, hTS⟩ := exists_lower_normalization hGram
  have hS := hGram.det_pos
  have hA : 0 ≤ blockChartBound ε (Matrix.of X') * (gramS X').det ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg (RealBlockLimit.blockChartBound_nonneg ε _) (Real.rpow_nonneg hS.le _)
  have hcancel : (gramS X').det ^ (-(1 / 2 : ℝ)) * (gramS X').det ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hS, neg_add_cancel, Real.rpow_zero]
  simp only [blockChartBound_cons ε X' hT hTS, ENNReal.ofReal_mul hA]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_first_row ε hTS, ← mul_assoc,
    ← ENNReal.ofReal_mul hA, mul_assoc, hcancel, mul_one]

private theorem lintegral_eq_cons (F : (Fin (k + 1) → Fin a → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ X, F X = ∫⁻ X' : Fin k → Fin a → ℝ, ∫⁻ x : Fin a → ℝ, F (Fin.cons x X') := by
  have hmp := measurePreserving_piFinSuccAbove
    (fun _ : Fin (k + 1) => (volume : Measure (Fin a → ℝ))) 0
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => Fin a → ℝ) 0 with he
  rw [volume_pi, ← hmp.symm.lintegral_comp_emb e.symm.measurableEmbedding F,
    lintegral_prod_symm' (fun p => F (e.symm p)) (hF.comp e.symm.measurable)]
  have hcons (x : Fin a → ℝ) (X' : Fin k → Fin a → ℝ) : e.symm (x, X') = Fin.cons x X' := by
    funext j
    refine Fin.cases ?_ (fun j' => ?_) j
    · simp [he, MeasurableEquiv.piFinSuccAbove]
    · simp [he, MeasurableEquiv.piFinSuccAbove]
  simp only [hcons]
  rfl

private theorem blockChartBound_zero_rows (ε : Fin a → ℝ) (X : Fin 0 → Fin a → ℝ) :
    blockChartBound ε (Matrix.of X) = 1 := by
  have hcol (l : Fin a) : colGram (Matrix.of X) l = 1 := by
    have h : (colsUpTo (Matrix.of X) l)ᵀ * colsUpTo (Matrix.of X) l = 0 := by
      ext i j
      simp [Matrix.mul_apply]
    rw [colGram, h, add_zero, Matrix.det_one]
  simp [blockChartBound, hcol]

private theorem integrable_rows (ε : Fin a → ℝ)
    (hε : ∀ j : Fin a, ∑ l : Fin a, (if j ≤ l then ε l + 1 / 2 else 0) < 0) (k : ℕ) :
    Integrable fun X : Fin k → Fin a → ℝ => blockChartBound ε (Matrix.of X) := by
  have hC : rowIntegral ε < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ (partialProduct_nonneg ε))).mp
      (integrable_partialProduct ε hε).2
  induction k with
  | zero =>
    have : IsFiniteMeasure (volume : Measure (Fin 0 → Fin a → ℝ)) :=
      ⟨by rw [volume_pi, Measure.pi_univ]; simp⟩
    simp only [blockChartBound_zero_rows]
    exact integrable_const 1
  | succ k ih =>
    refine ⟨(continuous_blockChartBound ε).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun X => RealBlockLimit.blockChartBound_nonneg ε (Matrix.of X)),
      lintegral_eq_cons (fun X => ENNReal.ofReal (blockChartBound ε (Matrix.of X)))
        (ENNReal.measurable_ofReal.comp (continuous_blockChartBound ε).measurable)]
    simp only [lintegral_cons]
    rw [lintegral_mul_const' _ _ hC.ne]
    exact ENNReal.mul_lt_top
      ((hasFiniteIntegral_iff_ofReal (ae_of_all _ fun X =>
        RealBlockLimit.blockChartBound_nonneg ε (Matrix.of X))).mp ih.2) hC

end RealBlockChartProof

/-- The real block chart bound is integrable under the strict tail condition. -/
theorem realBlockChartIntegrable : RealBlockChartIntegrableStatement := by
  intro a k ε hε
  exact RealBlockChartProof.integrable_rows ε hε k

end Langlands.Archimedean
