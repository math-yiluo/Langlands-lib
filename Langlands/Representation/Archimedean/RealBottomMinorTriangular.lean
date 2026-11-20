import Langlands.Representation.Archimedean.RealBottomMinorProducts
import Langlands.Representation.Archimedean.RealBlockFourierFinite

/-! # Triangular support of real products of compound matrices -/

noncomputable section

open Finset Matrix
open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean.RealBottomMinorTriangular

open Langlands.GeneralLinear
open RealBottomMinorProducts RealPrincipalSeriesDuality RealTiedMinorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n q : ℕ} {degree : Fin q → ℕ}

/-- The sum of the numerical indices over a family of subsets. -/
def indexSum (C : Selection n degree) : ℕ :=
  ∑ t, ∑ i ∈ (C t).val, i.val

/-- The number of members of the family containing a given column. -/
def columnWeight (C : Selection n degree) (j : Fin n) : ℕ :=
  (univ.filter fun t => j ∈ (C t).val).card

theorem columnWeight_eq_sum (C : Selection n degree) (j : Fin n) :
    columnWeight C j = ∑ t, if j ∈ (C t).val then 1 else 0 := by
  rw [columnWeight, card_eq_sum_ones, sum_filter]

private theorem minor_upper_ne_zero {d : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsUpperTriangular) {B C : {s : Finset (Fin n) // s.card = d}}
    (h : CompoundMinorProduct.minor A B C ≠ 0) :
    (∑ i ∈ B.val, i.val) ≤ (∑ i ∈ C.val, i.val) ∧
      ((∑ i ∈ B.val, i.val) = (∑ i ∈ C.val, i.val) → B = C) := by
  classical
  let b := B.val.orderEmbOfFin B.property
  let c := C.val.orderEmbOfFin C.property
  change (A.submatrix b c).det ≠ 0 at h
  rw [Matrix.det_apply] at h
  obtain ⟨σ, _, hσ⟩ := exists_ne_zero_of_sum_ne_zero h
  have hp : (∏ i, A (b (σ i)) (c i)) ≠ 0 := by
    intro hz
    apply hσ
    change Equiv.Perm.sign σ • (∏ i, A (b (σ i)) (c i)) = 0
    rw [hz, smul_zero]
  rw [prod_ne_zero_iff] at hp
  have hle (i : Fin d) : (b (σ i)).val ≤ (c i).val := by
    by_contra! hlt
    exact hp i (mem_univ i) (hA hlt)
  have hb : ∑ i, (b (σ i)).val = ∑ j ∈ B.val, j.val := by
    rw [Equiv.sum_comp σ (fun i => (b i).val), ← map_orderEmbOfFin_univ B.val B.property,
      sum_map]
    rfl
  have hc : ∑ i, (c i).val = ∑ j ∈ C.val, j.val := by
    rw [← map_orderEmbOfFin_univ C.val C.property, sum_map]
    rfl
  refine ⟨?_, fun he => ?_⟩
  · rw [← hb, ← hc]
    exact sum_le_sum fun i _ => hle i
  rw [← hb, ← hc] at he
  have hEq : ∀ i, b (σ i) = c i := fun i =>
    Fin.ext ((sum_eq_sum_iff_of_le (fun i _ => hle i)).mp he i (mem_univ i))
  apply Subtype.ext
  rw [← map_orderEmbOfFin_univ B.val B.property, ← map_orderEmbOfFin_univ C.val C.property]
  ext j
  simp only [mem_map, mem_univ, true_and, RelEmbedding.coe_toEmbedding]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨σ.symm i, by rw [← hEq, Equiv.apply_symm_apply]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨σ i, hEq i⟩

/-- A nonzero entry of the product on an upper triangular matrix has weakly
increasing index sum. Equality of the sums forces equality of the configurations. -/
theorem matrix_upper_ne_zero {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsUpperTriangular)
    {B C : Selection n degree} (h : CompoundMinorProduct.matrix degree A B C ≠ 0) :
    indexSum B ≤ indexSum C ∧ (indexSum B = indexSum C → B = C) := by
  rw [CompoundMinorProduct.matrix, prod_ne_zero_iff] at h
  have ht (t : Fin q) := minor_upper_ne_zero hA (h t (mem_univ t))
  exact ⟨sum_le_sum fun t _ => (ht t).1, fun he =>
    funext fun t => (ht t).2 ((sum_eq_sum_iff_of_le (fun t _ => (ht t).1)).mp he t (mem_univ t))⟩

private theorem coefficient_upperUnipotent (u : upperUnipotent n ℝ)
    (B C : Selection n degree) (hBC : indexSum C ≤ indexSum B) :
    coefficient B C (u : Langlands.GeneralLinear n ℝ) = if B = C then 1 else 0 := by
  split_ifs with he
  · subst B
    rw [coefficient_eq_prod, prod_apply]
    apply prod_eq_one
    intro t _
    unfold minorG
    rw [MatrixMinor.minor_of_isUpperTriangular u.property.1]
    simp only [u.property.2, prod_const_one, Complex.ofReal_one]
  · by_contra hn
    have h : CompoundMinorProduct.matrix degree
        ((u : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) B C ≠ 0 := by
      intro h0
      apply hn
      rw [coefficient, h0, Complex.ofReal_zero]
    have hl := matrix_upper_ne_zero u.property.1 h
    exact he (hl.2 (le_antisymm hl.1 hBC))

private theorem hasDerivAt_coefficient_curve (B C : Selection n degree)
    {γ : ℝ → Langlands.GeneralLinear n ℝ} (hγ0 : γ 0 = 1)
    {X : Matrix (Fin n) (Fin n) ℝ}
    (hγ : HasDerivAt (fun t => (γ t : Matrix (Fin n) (Fin n) ℝ)) X 0) :
    HasDerivAt (fun t => coefficient B C (γ t))
      (rightDerivative (matrixModel ℝ n) X (coefficient B C) 1) 0 := by
  have hsm := contMDiff_coefficient B C
  rw [rightDerivative_eq_fderiv hsm, Units.val_one, one_mul]
  have hd := differentiableAt_unitsExtension hsm ((γ 0).isUnit)
  have hc := hd.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ
  simpa only [Function.comp_def, unitsExtension_val, hγ0, Units.val_one] using hc

/-- A strictly upper triangular direction can contribute only from a smaller
row index sum to a larger column index sum. -/
theorem rightDerivative_coefficient_strictUpper_zero
    (B C : Selection n degree) (X : Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j : Fin n, (j : ℕ) ≤ i → X i j = 0)
    (hBC : indexSum C ≤ indexSum B) :
    rightDerivative (matrixModel ℝ n) X (coefficient B C) 1 = 0 := by
  let u := unipotentLine X (fun {i j} hij => hX i j hij.le) (fun i => hX i i le_rfl)
  let γ : ℝ → Langlands.GeneralLinear n ℝ := fun t => u t
  have hγ0 : γ 0 = 1 := by
    apply Units.ext
    simp only [γ, u, unipotentLine_val, zero_smul, add_zero, Units.val_one]
  have hγ : HasDerivAt (fun t => (γ t : Matrix (Fin n) (Fin n) ℝ)) X 0 := by
    simp only [γ, u, unipotentLine_val]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add 1
  have h := hasDerivAt_coefficient_curve B C hγ0 hγ
  have hconst : (fun t => coefficient B C (γ t)) = fun _ : ℝ => if B = C then 1 else 0 :=
    funext fun t => coefficient_upperUnipotent (u t) B C hBC
  rw [hconst] at h
  exact h.unique (hasDerivAt_const _ _)

/-- At a diagonal matrix the compound product is diagonal with the
corresponding diagonal factors. -/
theorem coefficient_diagonal (B C : Selection n degree) (a : Fin n → ℝˣ) :
    coefficient B C (Iwasawa.diagonalUnits a) =
      if B = C then diagonalFactor C a else 0 := by
  simp only [coefficient, Iwasawa.diagonalUnits_val, CompoundMinorProduct.matrix_diagonal,
    Matrix.diagonal_apply, diagonalFactor]
  split_ifs with h
  · subst B
    simp only [Complex.ofReal_prod]
  · exact Complex.ofReal_zero

private theorem diagonalFactor_single (C : Selection n degree) (j : Fin n) (z : ℝˣ) :
    diagonalFactor C (fun i => if i = j then z else 1) =
      ((z : ℝ) : ℂ) ^ columnWeight C j := by
  rw [diagonalFactor, columnWeight_eq_sum, ← prod_pow_eq_pow_sum]
  apply prod_congr rfl
  intro t _
  by_cases hj : j ∈ (C t).val
  · rw [ite_eq_left hj, pow_one, prod_eq_single j]
    · simp
    · intro i _ hi
      simp [hi]
    · exact fun h => (h hj).elim
  · rw [ite_eq_right hj, pow_zero]
    exact prod_eq_one fun i hi => by
      have hij : i ≠ j := fun he => hj (he ▸ hi)
      simp [hij]

/-- The diagonal matrix unit acts on a column configuration by its
column occurrence count. -/
theorem rightDerivative_coefficient_diagonal (B C : Selection n degree) (j : Fin n) :
    rightDerivative (matrixModel ℝ n) (Matrix.single j j 1) (coefficient B C) 1 =
      if B = C then (columnWeight C j : ℂ) else 0 := by
  let X : Matrix (Fin n) (Fin n) ℝ := Matrix.single j j 1
  have hd := hasDerivAt_mul_matrixExpUnit_smul
    ((contMDiff_coefficient B C).of_le (mod_cast le_top)) (1 : Langlands.GeneralLinear n ℝ) X
  have hEval (s : ℝ) : coefficient B C (1 * matrixExpUnit n (s • X)) =
      if B = C then Complex.exp ((s : ℂ) * (columnWeight C j : ℂ)) else 0 := by
    have hX : s • X = Matrix.diagonal fun i => if i = j then s else 0 := by
      ext i k
      simp only [X, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply, Matrix.diagonal_apply]
      by_cases hi : i = j
      · subst i
        by_cases hk : k = j
        · subst k
          simp
        · simp [Ne.symm hk]
      · simp [hi, Ne.symm hi]
    rw [one_mul, hX, matrixExpUnit_diagonal, coefficient_diagonal]
    split_ifs with h
    · let z := Units.mk0 (Real.exp s) (Real.exp_pos s).ne'
      have ha : (fun i : Fin n => Units.mk0 (Real.exp (if i = j then s else 0))
          (Real.exp_pos _).ne') = fun i => if i = j then z else 1 := by
        funext i
        apply Units.ext
        by_cases hi : i = j <;> simp [hi, z]
      rw [ha, diagonalFactor_single]
      change ((Real.exp s : ℝ) : ℂ) ^ columnWeight C j = _
      rw [← Complex.cpow_natCast, ofReal_exp_cpow]
    · rfl
  simp_rw [hEval] at hd
  change rightDerivative (matrixModel ℝ n) X (coefficient B C) 1 = _
  by_cases h : B = C
  · simp only [ite_eq_left h] at hd ⊢
    have hExp := (((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const
      (columnWeight C j : ℂ)).cexp)
    exact hd.unique (by simpa using hExp)
  · simp only [ite_eq_right h] at hd ⊢
    exact hd.unique (hasDerivAt_const _ _)

/-- The sign reflection at a column acts by its column occurrence parity. -/
theorem coefficient_signReflection (B C : Selection n degree) (j : Fin n) :
    coefficient B C (Unitary.toUnits (signReflection n j)) =
      if B = C then (-1 : ℂ) ^ columnWeight C j else 0 := by
  rw [RealBlockFourierFinite.toUnits_signReflection, coefficient_diagonal]
  split_ifs
  · change diagonalFactor C (fun i => if i = j then (-1 : ℝˣ) else 1) = _
    rw [diagonalFactor_single]
    simp
  · rfl

end Langlands.Archimedean.RealBottomMinorTriangular
