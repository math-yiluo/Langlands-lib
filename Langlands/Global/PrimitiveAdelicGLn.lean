import Langlands.Global.PrimitiveAdelicGL2

/-! # Height reduction for the actual adelic `GL(n)` -/

noncomputable section

universe u

open scoped NNReal Matrix

namespace Langlands.Global.PrimitiveAdelicHeight

open NumberField

/-! ## A local completion of a column of maximum norm one -/

section Local

variable {K : Type*} [NormedField K] {p : ℕ}

/-- An index of a coordinate of maximal norm. -/
def maxIndex (z : Fin (p + 1) → K) : Fin (p + 1) :=
  (Finset.univ.exists_max_image (fun i => ‖z i‖) Finset.univ_nonempty).choose

theorem norm_le_norm_maxIndex (z : Fin (p + 1) → K) (i : Fin (p + 1)) :
    ‖z i‖ ≤ ‖z (maxIndex z)‖ :=
  (Finset.univ.exists_max_image (fun i => ‖z i‖) Finset.univ_nonempty).choose_spec.2 i
    (Finset.mem_univ i)

theorem norm_maxIndex (z : Fin (p + 1) → K) : ‖z (maxIndex z)‖ = ‖z‖ :=
  le_antisymm (norm_le_pi_norm z _)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (norm_le_norm_maxIndex z))

/-- The matrix with first column `w` and the standard basis vectors as its other
columns. -/
def firstColumnMatrix {R : Type*} [Zero R] [One R] (w : Fin (p + 1) → R) :
    Matrix (Fin (p + 1)) (Fin (p + 1)) R :=
  Matrix.of fun i c => if c = 0 then w i else if i = c then 1 else 0

theorem det_firstColumnMatrix {R : Type*} [CommRing R] (w : Fin (p + 1) → R) :
    (firstColumnMatrix w).det = w 0 := by
  have hlow : (firstColumnMatrix w).IsLowerTriangular := by
    intro i c h
    have h' : i < c := OrderDual.toDual_lt_toDual.mp h
    have hc : c ≠ 0 := (lt_of_le_of_lt (Fin.zero_le i) h').ne'
    simp [firstColumnMatrix, hc, h'.ne]
  rw [Matrix.det_of_isLowerTriangular _ hlow, Fin.prod_univ_succ]
  simp [firstColumnMatrix, Fin.succ_ne_zero]

/-- The local completion of a column: the coordinates are permuted so that one of
maximal norm comes first, the first column is completed by standard basis
vectors, and the coordinates are permuted back. -/
def localCompletion (z : Fin (p + 1) → K) : Matrix (Fin (p + 1)) (Fin (p + 1)) K :=
  (firstColumnMatrix (z ∘ Equiv.swap 0 (maxIndex z))).submatrix
    (Equiv.swap 0 (maxIndex z)) id

theorem localCompletion_apply (z : Fin (p + 1) → K) (i c : Fin (p + 1)) :
    localCompletion z i c =
      if c = 0 then z i else if Equiv.swap 0 (maxIndex z) i = c then 1 else 0 := by
  simp [localCompletion, firstColumnMatrix, Equiv.swap_apply_self]

theorem localCompletion_zero (z : Fin (p + 1) → K) (i : Fin (p + 1)) :
    localCompletion z i 0 = z i := by
  rw [localCompletion_apply, ite_eq_left rfl]

theorem det_localCompletion (z : Fin (p + 1) → K) :
    (localCompletion z).det =
      Equiv.Perm.sign (Equiv.swap 0 (maxIndex z)) * z (maxIndex z) := by
  rw [localCompletion, Matrix.det_permute, det_firstColumnMatrix, Function.comp_apply,
    Equiv.swap_apply_left]

theorem norm_det_localCompletion (z : Fin (p + 1) → K) :
    ‖(localCompletion z).det‖ = ‖z‖ := by
  rw [det_localCompletion, norm_mul, norm_maxIndex]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap (0 : Fin (p + 1)) (maxIndex z)))
    with h | h <;> simp [h]

theorem norm_localCompletion_le (z : Fin (p + 1) → K) (hz : ‖z‖ ≤ 1) (i c : Fin (p + 1)) :
    ‖localCompletion z i c‖ ≤ 1 := by
  rw [localCompletion_apply]
  split_ifs
  · exact (norm_le_pi_norm z i).trans hz
  · simp
  · simp

end Local

/-! ## Block matrices -/

section Block

variable {R : Type*} {p : ℕ}

/-- The lower right block of a square matrix of size `p + 1`. -/
def lowerBlock (M : Matrix (Fin (p + 1)) (Fin (p + 1)) R) : Matrix (Fin p) (Fin p) R :=
  M.submatrix Fin.succ Fin.succ

/-- The block diagonal matrix `diag(1, A)`. -/
def extendMatrix [Zero R] [One R] (A : Matrix (Fin p) (Fin p) R) :
    Matrix (Fin (p + 1)) (Fin (p + 1)) R :=
  Matrix.of fun i j =>
    Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => A i' j') j) i

section Apply

variable [Zero R] [One R] (A : Matrix (Fin p) (Fin p) R)

@[simp] theorem extendMatrix_zero_zero : extendMatrix A 0 0 = 1 := rfl

@[simp] theorem extendMatrix_zero_succ (j : Fin p) : extendMatrix A 0 j.succ = 0 := rfl

@[simp] theorem extendMatrix_succ_zero (i : Fin p) : extendMatrix A i.succ 0 = 0 := rfl

@[simp] theorem extendMatrix_succ_succ (i j : Fin p) : extendMatrix A i.succ j.succ = A i j :=
  rfl

theorem lowerBlock_extendMatrix : lowerBlock (extendMatrix A) = A := by
  ext i j
  rfl

end Apply

section Ring

variable [CommRing R]

theorem det_eq_mul_det_lowerBlock (M : Matrix (Fin (p + 1)) (Fin (p + 1)) R)
    (h : ∀ i : Fin p, M i.succ 0 = 0) : M.det = M 0 0 * (lowerBlock M).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [h, lowerBlock, Fin.succAbove_zero]

theorem lowerBlock_mul (M N : Matrix (Fin (p + 1)) (Fin (p + 1)) R)
    (h : ∀ i : Fin p, M i.succ 0 = 0) : lowerBlock (M * N) = lowerBlock M * lowerBlock N := by
  ext i j
  rw [lowerBlock, Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_succ, h, zero_mul,
    zero_add]
  rfl

theorem mul_succ_zero (M N : Matrix (Fin (p + 1)) (Fin (p + 1)) R)
    (hM : ∀ i : Fin p, M i.succ 0 = 0) (hN : ∀ i : Fin p, N i.succ 0 = 0) (i : Fin p) :
    (M * N) i.succ 0 = 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ, hM, zero_mul, zero_add]
  exact Finset.sum_eq_zero fun l _ => by rw [hN, mul_zero]

theorem extendMatrix_mul (A B : Matrix (Fin p) (Fin p) R) :
    extendMatrix A * extendMatrix B = extendMatrix (A * B) := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem extendMatrix_one : extendMatrix (1 : Matrix (Fin p) (Fin p) R) = 1 := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [Matrix.one_apply, Fin.succ_ne_zero, fun i : Fin p => (Fin.succ_ne_zero i).symm]

theorem det_extendMatrix (A : Matrix (Fin p) (Fin p) R) : (extendMatrix A).det = A.det := by
  rw [det_eq_mul_det_lowerBlock _ (extendMatrix_succ_zero A), extendMatrix_zero_zero,
    one_mul, lowerBlock_extendMatrix]

theorem extendMatrix_mulVec_single (A : Matrix (Fin p) (Fin p) R) :
    extendMatrix A *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  rw [Matrix.mulVec_single_one]
  funext i
  cases i using Fin.cases <;> simp [Matrix.col, Fin.succ_ne_zero]

theorem map_extendMatrix {S : Type*} [CommRing S] (f : R →+* S)
    (A : Matrix (Fin p) (Fin p) R) : (extendMatrix A).map f = extendMatrix (A.map f) := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;> simp

variable (R p)

/-- The monoid embedding `A ↦ diag(1, A)` of square matrices. -/
def extendHom : Matrix (Fin p) (Fin p) R →* Matrix (Fin (p + 1)) (Fin (p + 1)) R where
  toFun := extendMatrix
  map_one' := extendMatrix_one
  map_mul' A B := (extendMatrix_mul A B).symm

/-- The embedding `g ↦ diag(1, g)` of general linear groups. -/
def extendGL : Matrix.GeneralLinearGroup (Fin p) R →* Matrix.GeneralLinearGroup (Fin (p + 1)) R :=
  Units.map (extendHom R p)

variable {R p}

@[simp] theorem extendGL_val (g : Matrix.GeneralLinearGroup (Fin p) R) :
    (extendGL R p g).val = extendMatrix g.val := rfl

end Ring

end Block

/-! ## Entry bounds under ring homomorphisms to normed fields -/

section Bounds

variable {R K : Type*} [CommRing R] [NormedField K] (f : R →+* K)

theorem norm_map_mul_apply_le_one [IsUltrametricDist K] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) R) (hA : ∀ i j, ‖f (A i j)‖ ≤ 1)
    (hB : ∀ i j, ‖f (B i j)‖ ≤ 1) (i j : Fin n) : ‖f ((A * B) i j)‖ ≤ 1 := by
  rw [Matrix.mul_apply, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun l _ => ?_
  rw [map_mul, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hA i l)).trans (hB l j)

theorem norm_map_mul_apply_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) {a b : ℝ}
    (ha : 0 ≤ a) (hA : ∀ i j, ‖f (A i j)‖ ≤ a) (hB : ∀ i j, ‖f (B i j)‖ ≤ b)
    (i j : Fin n) : ‖f ((A * B) i j)‖ ≤ n * (a * b) := by
  rw [Matrix.mul_apply, map_sum]
  calc ‖∑ l, f (A i l * B l j)‖
      ≤ ∑ l, ‖f (A i l * B l j)‖ := norm_sum_le _ _
    _ ≤ ∑ _l : Fin n, a * b := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [map_mul, norm_mul]
        exact mul_le_mul (hA i l) (hB l j) (norm_nonneg _) ha
    _ = n * (a * b) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem norm_map_extendMatrix_le {p : ℕ} (A : Matrix (Fin p) (Fin p) R) {B : ℝ}
    (hB : 1 ≤ B) (hA : ∀ i j, ‖f (A i j)‖ ≤ B) (i j : Fin (p + 1)) :
    ‖f (extendMatrix A i j)‖ ≤ B := by
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [hB, hA, zero_le_one.trans hB]

theorem norm_map_one_le {n : ℕ} (i j : Fin n) :
    ‖f ((1 : Matrix (Fin n) (Fin n) R) i j)‖ ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

end Bounds

variable (F : Type u) [Field F] [NumberField F]

/-! ## Bounded unimodular factors and reduced triangular factors -/

/-- An actual adelic matrix whose entries are integral at every finite place and
bounded by `B` at every infinite place, and whose determinant has local norm one at
every place. -/
def IsBoundedUnimodular (n : ℕ) (B : ℝ) (k : AdelicGL F n) : Prop :=
  (∀ v i j, ‖finiteProjection F v (k i j)‖ ≤ 1) ∧
    (∀ w i j, ‖infiniteProjection F w (k i j)‖ ≤ B) ∧
    (∀ v, ‖finiteProjection F v (Matrix.GeneralLinearGroup.det k).val‖ = 1) ∧
    ∀ w, ‖infiniteProjection F w (Matrix.GeneralLinearGroup.det k).val‖ = 1

/-- An actual upper triangular adelic matrix whose diagonal entries are ideles
`t i` with `|t i| ≤ c |t (i + 1)|` for the normalized idele absolute value. -/
def IsReducedTriangular (n : ℕ) (c : ℝ) (b : AdelicGL F n) : Prop :=
  b.val.IsUpperTriangular ∧ ∃ t : Fin n → Ideles F, (∀ i, b i i = (t i).val) ∧
    ∀ i j : Fin n, i.val + 1 = j.val →
      ((IdeleAbsoluteValue.full F (t i) : ℝ≥0) : ℝ) ≤
        c * ((IdeleAbsoluteValue.full F (t j) : ℝ≥0) : ℝ)

/-- Reduction with constants `c` and `B` in rank `n`: every actual adelic matrix,
after right multiplication by a rational invertible matrix, is a bounded unimodular
matrix times a reduced upper triangular matrix. -/
def HasReduction (n : ℕ) (c B : ℝ) : Prop :=
  ∀ g : AdelicGL F n, ∃ (γ : RationalGL F n) (k b : AdelicGL F n),
    g * AdelicGL.rational F n γ = k * b ∧ IsBoundedUnimodular F n B k ∧
      IsReducedTriangular F n c b

theorem isBoundedUnimodular_one (n : ℕ) : IsBoundedUnimodular F n 1 1 := by
  refine ⟨fun v i j => norm_map_one_le (finiteProjection F v) i j,
    fun w i j => norm_map_one_le (infiniteProjection F w) i j, fun v => ?_, fun w => ?_⟩
  · rw [map_one, Units.val_one, map_one, norm_one]
  · rw [map_one, Units.val_one, map_one, norm_one]

theorem IsBoundedUnimodular.mul_extendGL {p : ℕ} {B : ℝ} {k₁ : AdelicGL F (p + 1)}
    {k' : AdelicGL F p} (h₁ : IsBoundedUnimodular F (p + 1) 1 k₁)
    (h' : IsBoundedUnimodular F p B k') (hB : 1 ≤ B) :
    IsBoundedUnimodular F (p + 1) ((p + 1 : ℕ) * B) (k₁ * extendGL (Adeles F) p k') := by
  obtain ⟨hf₁, hi₁, hdf₁, hdi₁⟩ := h₁
  obtain ⟨hf', hi', hdf', hdi'⟩ := h'
  have hdet : (Matrix.GeneralLinearGroup.det (k₁ * extendGL (Adeles F) p k')).val =
      (Matrix.GeneralLinearGroup.det k₁).val * (Matrix.GeneralLinearGroup.det k').val := by
    rw [map_mul, Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
      extendGL_val, det_extendMatrix]
  refine ⟨fun v i j => ?_, fun w i j => ?_, fun v => ?_, fun w => ?_⟩
  · exact norm_map_mul_apply_le_one (finiteProjection F v) _ _ (hf₁ v)
      (norm_map_extendMatrix_le (finiteProjection F v) k'.val le_rfl (hf' v)) i j
  · have h := norm_map_mul_apply_le (infiniteProjection F w) k₁.val
      (extendGL (Adeles F) p k').val zero_le_one (hi₁ w)
      (norm_map_extendMatrix_le (infiniteProjection F w) k'.val hB (hi' w)) i j
    rwa [one_mul] at h
  · rw [hdet, map_mul, norm_mul, hdf₁, hdf', one_mul]
  · rw [hdet, map_mul, norm_mul, hdi₁, hdi', one_mul]

/-! ## The adelic completion of a normalized column -/

/-- The actual adelic matrix whose local components are the local completions of
the local components of `y`. Its entries are entries of `y`, `0` or `1`. -/
def columnCompletion {p : ℕ} (y : Vector F (p + 1)) :
    Matrix (Fin (p + 1)) (Fin (p + 1)) (Adeles F) :=
  Matrix.of fun i c =>
    (fun w => localCompletion (fun l => infiniteProjection F w (y l)) i c,
      ⟨fun v => localCompletion (fun l => finiteProjection F v (y l)) i c, by
        filter_upwards [(y i).2.2] with v hv
        simp only [localCompletion_apply]
        split_ifs
        · exact hv
        · exact one_mem _
        · exact zero_mem _⟩)

variable {F} in
theorem finiteProjection_columnCompletion {p : ℕ} (y : Vector F (p + 1)) (v : FinitePlace F)
    (i c : Fin (p + 1)) :
    finiteProjection F v (columnCompletion F y i c) =
      localCompletion (fun l => finiteProjection F v (y l)) i c := rfl

variable {F} in
theorem infiniteProjection_columnCompletion {p : ℕ} (y : Vector F (p + 1))
    (w : InfinitePlace F) (i c : Fin (p + 1)) :
    infiniteProjection F w (columnCompletion F y i c) =
      localCompletion (fun l => infiniteProjection F w (y l)) i c := rfl

theorem columnCompletion_zero {p : ℕ} (y : Vector F (p + 1)) (i : Fin (p + 1)) :
    columnCompletion F y i 0 = y i := by
  refine Prod.ext (funext fun w => ?_) (Subtype.ext (funext fun v => ?_))
  · exact localCompletion_zero (fun l => infiniteProjection F w (y l)) i
  · exact localCompletion_zero (fun l => finiteProjection F v (y l)) i

theorem finiteProjection_det_columnCompletion {p : ℕ} (y : Vector F (p + 1))
    (v : FinitePlace F) :
    finiteProjection F v (columnCompletion F y).det =
      (localCompletion (fun l => finiteProjection F v (y l))).det := by
  rw [RingHom.map_det]
  rfl

theorem infiniteProjection_det_columnCompletion {p : ℕ} (y : Vector F (p + 1))
    (w : InfinitePlace F) :
    infiniteProjection F w (columnCompletion F y).det =
      (localCompletion (fun l => infiniteProjection F w (y l))).det := by
  rw [RingHom.map_det]
  rfl

theorem isUnit_columnCompletion {p : ℕ} (y : Vector F (p + 1))
    (hfin : ∀ v, finiteNorm F (p + 1) y v = 1) (hinf : ∀ w, infiniteNorm F (p + 1) y w = 1) :
    IsUnit (columnCompletion F y) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  refine isUnit_of_local_norm F _ (fun v => ?_) fun w => ?_
  · rw [finiteProjection_det_columnCompletion, norm_det_localCompletion]
    exact hfin v
  · apply norm_ne_zero_iff.mp
    rw [infiniteProjection_det_columnCompletion, norm_det_localCompletion]
    change infiniteNorm F (p + 1) y w ≠ 0
    rw [hinf w]
    exact one_ne_zero

/-! ## The leading column decomposition -/

theorem rational_firstVector (p : ℕ) :
    rational F (p + 1) (firstVector F (p + 1) p.succ_pos) = Pi.single 0 1 := by
  have h0 : (⟨0, p.succ_pos⟩ : Fin (p + 1)) = 0 := rfl
  funext i
  by_cases hi : i = 0
  · subst hi
    simp [rational, firstVector, h0]
  · simp [rational, firstVector, h0, hi]

variable {F}

/-- The first column of an actual adelic matrix, a primitive vector. -/
def leadingColumn {p : ℕ} (g : AdelicGL F (p + 1)) : Vector F (p + 1) :=
  g.val *ᵥ rational F (p + 1) (firstVector F (p + 1) p.succ_pos)

theorem leadingColumn_isPrimitive {p : ℕ} (g : AdelicGL F (p + 1)) :
    IsPrimitive F (p + 1) (leadingColumn g) :=
  ⟨g, _, firstVector_ne_zero F (p + 1) p.succ_pos, rfl⟩

/-- The actual content idele of the first column. -/
def leadingContent {p : ℕ} (g : AdelicGL F (p + 1)) : Ideles F :=
  contentIdele F (p + 1) (leadingColumn g) (leadingColumn_isPrimitive g)

/-- The first column divided by its content idele. -/
def leadingDirection {p : ℕ} (g : AdelicGL F (p + 1)) : Vector F (p + 1) :=
  normalizedVector F (p + 1) (leadingColumn g) (leadingColumn_isPrimitive g)

/-- The bounded unimodular factor: the completion of the normalized first column. -/
def leadingFactor {p : ℕ} (g : AdelicGL F (p + 1)) : AdelicGL F (p + 1) :=
  (isUnit_columnCompletion F (leadingDirection g) (finiteNorm_normalizedVector F _ _ _)
    (infiniteNorm_normalizedVector F _ _ _)).unit

/-- The remaining factor `k⁻¹ g`, whose first column is `leadingContent g` times the
first standard vector. -/
def leadingRemainder {p : ℕ} (g : AdelicGL F (p + 1)) : AdelicGL F (p + 1) :=
  (leadingFactor g)⁻¹ * g

theorem leadingFactor_val {p : ℕ} (g : AdelicGL F (p + 1)) :
    (leadingFactor g).val = columnCompletion F (leadingDirection g) := rfl

theorem leadingFactor_mul_leadingRemainder {p : ℕ} (g : AdelicGL F (p + 1)) :
    leadingFactor g * leadingRemainder g = g :=
  mul_inv_cancel_left _ _

theorem leadingFactor_mulVec_first {p : ℕ} (g : AdelicGL F (p + 1)) :
    (leadingFactor g).val *ᵥ Pi.single 0 1 = leadingDirection g := by
  rw [Matrix.mulVec_single_one, leadingFactor_val]
  funext i
  exact columnCompletion_zero F _ i

theorem leadingRemainder_mulVec_first {p : ℕ} (g : AdelicGL F (p + 1)) :
    (leadingRemainder g).val *ᵥ Pi.single 0 1 =
      (leadingContent g).val • (Pi.single 0 1 : Vector F (p + 1)) := by
  have hc : g.val *ᵥ Pi.single 0 1 = (leadingContent g).val • leadingDirection g := by
    rw [← rational_firstVector F p]
    exact (contentIdele_smul_normalizedVector F (p + 1) _ _).symm
  rw [leadingRemainder, Units.val_mul, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul,
    ← leadingFactor_mulVec_first g, Matrix.mulVec_mulVec, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem leadingRemainder_zero_zero {p : ℕ} (g : AdelicGL F (p + 1)) :
    leadingRemainder g 0 0 = (leadingContent g).val := by
  have h := congrFun (leadingRemainder_mulVec_first g) 0
  rw [Matrix.mulVec_single_one] at h
  simpa using h

theorem leadingRemainder_succ_zero {p : ℕ} (g : AdelicGL F (p + 1)) (i : Fin p) :
    leadingRemainder g i.succ 0 = 0 := by
  have h := congrFun (leadingRemainder_mulVec_first g) i.succ
  rw [Matrix.mulVec_single_one] at h
  simpa [Fin.succ_ne_zero] using h

theorem isUnit_lowerBlock_leadingRemainder {p : ℕ} (g : AdelicGL F (p + 1)) :
    IsUnit (lowerBlock (leadingRemainder g).val) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have h : IsUnit (leadingRemainder g).val.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (leadingRemainder g).isUnit
  rw [det_eq_mul_det_lowerBlock _ (leadingRemainder_succ_zero g)] at h
  exact isUnit_of_mul_isUnit_right h

/-- The lower right block of the remaining factor, an actual adelic matrix of
rank one less. -/
def lowerRemainder {p : ℕ} (g : AdelicGL F (p + 1)) : AdelicGL F p :=
  (isUnit_lowerBlock_leadingRemainder g).unit

theorem lowerRemainder_val {p : ℕ} (g : AdelicGL F (p + 1)) :
    (lowerRemainder g).val = lowerBlock (leadingRemainder g).val := rfl

theorem rationalHeight_leading {p : ℕ} (g : AdelicGL F (p + 1)) :
    rationalHeight F (p + 1) g (firstVector F (p + 1) p.succ_pos) =
      ((IdeleAbsoluteValue.full F (leadingContent g) : ℝ≥0) : ℝ) := by
  rw [leadingContent, full_contentIdele, positiveHeight_val]
  rfl

theorem isBoundedUnimodular_leadingFactor {p : ℕ} (g : AdelicGL F (p + 1)) :
    IsBoundedUnimodular F (p + 1) 1 (leadingFactor g) := by
  refine ⟨fun v i j => ?_, fun w i j => ?_, fun v => ?_, fun w => ?_⟩
  · rw [leadingFactor_val, finiteProjection_columnCompletion]
    exact norm_localCompletion_le _ (finiteNorm_normalizedVector F _ _ _ v).le i j
  · rw [leadingFactor_val, infiniteProjection_columnCompletion]
    exact norm_localCompletion_le _ (infiniteNorm_normalizedVector F _ _ _ w).le i j
  · rw [Matrix.GeneralLinearGroup.val_det_apply, leadingFactor_val,
      finiteProjection_det_columnCompletion, norm_det_localCompletion]
    exact finiteNorm_normalizedVector F _ _ _ v
  · rw [Matrix.GeneralLinearGroup.val_det_apply, leadingFactor_val,
      infiniteProjection_det_columnCompletion, norm_det_localCompletion]
    exact infiniteNorm_normalizedVector F _ _ _ w

/-! ## Rank-two vectors inside rank `p + 2` -/

/-- A rational vector supported on the first two coordinates. -/
def padRational {p : ℕ} (r : Fin 2 → F) : Fin (p + 2) → F :=
  Matrix.vecCons (r 0) (Matrix.vecCons (r 1) 0)

/-- An adelic vector supported on the first two coordinates. -/
def padVector {p : ℕ} (x : Vector F 2) : Vector F (p + 2) :=
  Matrix.vecCons (x 0) (Matrix.vecCons (x 1) 0)

omit [NumberField F] in
theorem padRational_ne_zero {p : ℕ} {r : Fin 2 → F} (hr : r ≠ 0) :
    (padRational r : Fin (p + 2) → F) ≠ 0 := by
  intro h
  apply hr
  funext i
  fin_cases i
  · simpa [padRational] using congrFun h 0
  · simpa [padRational] using congrFun h 1

theorem rational_padRational {p : ℕ} (r : Fin 2 → F) :
    rational F (p + 2) (padRational r) = padVector (rational F 2 r) := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i => simp [rational, padRational, padVector]

theorem norm_vecCons_vecCons_zero {E : Type*} [SeminormedAddCommGroup E] {p : ℕ} (a b : E) :
    ‖(Matrix.vecCons a (Matrix.vecCons b 0) : Fin (p + 2) → E)‖ = ‖(![a, b] : Fin 2 → E)‖ := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
    cases i using Fin.cases with
    | zero => simpa using norm_le_pi_norm (![a, b] : Fin 2 → E) 0
    | succ i =>
      cases i using Fin.cases with
      | zero => simpa using norm_le_pi_norm (![a, b] : Fin 2 → E) 1
      | succ i => simp
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
    fin_cases i
    · simpa using norm_le_pi_norm (Matrix.vecCons a (Matrix.vecCons b 0) : Fin (p + 2) → E) 0
    · simpa using norm_le_pi_norm (Matrix.vecCons a (Matrix.vecCons b 0) : Fin (p + 2) → E) 1

theorem norm_map_padVector {K : Type*} [NormedField K] (f : Adeles F →+* K) {p : ℕ}
    (x : Vector F 2) :
    ‖fun i : Fin (p + 2) => f (padVector x i)‖ = ‖fun i : Fin 2 => f (x i)‖ := by
  have h1 : (fun i : Fin (p + 2) => f (padVector x i)) =
      Matrix.vecCons (f (x 0)) (Matrix.vecCons (f (x 1)) 0) := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      cases i using Fin.cases with
      | zero => rfl
      | succ i => simp [padVector]
  have h2 : (fun i : Fin 2 => f (x i)) = ![f (x 0), f (x 1)] := by
    funext i
    fin_cases i <;> rfl
  rw [h1, h2, norm_vecCons_vecCons_zero]

theorem height_padVector {p : ℕ} (x : Vector F 2) :
    height F (p + 2) (padVector x) = height F 2 x := by
  have hfin : finiteNorm F (p + 2) (padVector x) = finiteNorm F 2 x := by
    funext v
    exact norm_map_padVector (finiteProjection F v) x
  have hinf : infiniteNorm F (p + 2) (padVector x) = infiniteNorm F 2 x := by
    funext w
    exact norm_map_padVector (infiniteProjection F w) x
  simp only [height, hfin, hinf]

/-- The upper left two-by-two block. -/
def upperBlockTwo {p : ℕ} (b : Matrix (Fin (p + 2)) (Fin (p + 2)) (Adeles F)) :
    Matrix (Fin 2) (Fin 2) (Adeles F) :=
  !![b 0 0, b 0 1; b 1 0, b 1 1]

theorem mulVec_padVector {p : ℕ} (b : Matrix (Fin (p + 2)) (Fin (p + 2)) (Adeles F))
    (h0 : ∀ i : Fin p, b i.succ.succ 0 = 0) (h1 : ∀ i : Fin p, b i.succ.succ 1 = 0)
    (x : Vector F 2) : b *ᵥ padVector x = padVector (upperBlockTwo b *ᵥ x) := by
  funext i
  have hsum : (b *ᵥ padVector x) i = b i 0 * x 0 + b i 1 * x 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, padVector]
  rw [hsum]
  cases i using Fin.cases with
  | zero => simp [padVector, upperBlockTwo, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  | succ i =>
    cases i using Fin.cases with
    | zero => simp [padVector, upperBlockTwo, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    | succ i => simp [padVector, h0, h1]

/-- **The rank-two step.** For a bounded unimodular `k` and an upper triangular
`b` with first diagonal ideles `t₀, t₁`, some nonzero rational vector has height
at most a fixed multiple of `√(|t₀| |t₁|)` under `k b`. -/
theorem exists_rationalHeight_le_of_triangular {p : ℕ} {B C : ℝ} (hB : 0 ≤ B)
    (hherm : ∀ g : AdelicGL F 2, ∃ r : Fin 2 → F, r ≠ 0 ∧
      rationalHeight F 2 g r ≤
        C * Real.sqrt ((IdeleAbsoluteValue.full F (Matrix.GeneralLinearGroup.det g) : ℝ≥0) : ℝ))
    {k b : AdelicGL F (p + 2)} (hk : IsBoundedUnimodular F (p + 2) B k)
    (hb : b.val.IsUpperTriangular) {t₀ t₁ : Ideles F} (h00 : b 0 0 = t₀.val)
    (h11 : b 1 1 = t₁.val) :
    ∃ v : Fin (p + 2) → F, v ≠ 0 ∧ rationalHeight F (p + 2) (k * b) v ≤
      (((p + 2 : ℕ) : ℝ) * B) ^ Module.finrank ℚ F *
        (C * Real.sqrt (((IdeleAbsoluteValue.full F t₀ : ℝ≥0) : ℝ) *
          ((IdeleAbsoluteValue.full F t₁ : ℝ≥0) : ℝ))) := by
  have h10 : b 1 0 = 0 := hb (show (0 : Fin (p + 2)) < 1 from Fin.zero_lt_one)
  have hdet : (upperBlockTwo b.val).det = (t₀ * t₁).val := by
    rw [upperBlockTwo, Matrix.det_fin_two_of, Units.val_mul]
    change b 0 0 * b 1 1 - b 0 1 * b 1 0 = _
    rw [h00, h11, h10, mul_zero, sub_zero]
  have hunit : IsUnit (upperBlockTwo b.val) := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet]
    exact (t₀ * t₁).isUnit
  set b₂ : AdelicGL F 2 := hunit.unit
  have hdet₂ : Matrix.GeneralLinearGroup.det b₂ = t₀ * t₁ := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact hdet
  obtain ⟨r, hr, hH⟩ := hherm b₂
  refine ⟨padRational r, padRational_ne_zero hr, ?_⟩
  have hlow0 (i : Fin p) : b i.succ.succ 0 = 0 :=
    hb (show (0 : Fin (p + 2)) < i.succ.succ from Fin.succ_pos _)
  have hlow1 (i : Fin p) : b i.succ.succ 1 = 0 := by
    refine hb (show (1 : Fin (p + 2)) < i.succ.succ from ?_)
    rw [← Fin.succ_zero_eq_one, Fin.succ_lt_succ_iff]
    exact Fin.succ_pos _
  have hbv : b.val *ᵥ rational F (p + 2) (padRational r) =
      padVector (b₂.val *ᵥ rational F 2 r) := by
    rw [rational_padRational]
    exact mulVec_padVector b.val hlow0 hlow1 _
  have hprim : IsPrimitive F (p + 2) (b.val *ᵥ rational F (p + 2) (padRational r)) :=
    ⟨b, _, padRational_ne_zero hr, rfl⟩
  have hk' := height_mulVec_le F k hB hk.1 hk.2.1 hprim
  have hfull : ((IdeleAbsoluteValue.full F (Matrix.GeneralLinearGroup.det b₂) : ℝ≥0) : ℝ) =
      ((IdeleAbsoluteValue.full F t₀ : ℝ≥0) : ℝ) *
        ((IdeleAbsoluteValue.full F t₁ : ℝ≥0) : ℝ) := by
    rw [hdet₂, map_mul, Units.val_mul, NNReal.coe_mul]
  rw [hfull] at hH
  calc rationalHeight F (p + 2) (k * b) (padRational r)
      = height F (p + 2) (k.val *ᵥ (b.val *ᵥ rational F (p + 2) (padRational r))) := by
        rw [rationalHeight, Units.val_mul, Matrix.mulVec_mulVec]
    _ ≤ (((p + 2 : ℕ) : ℝ) * B) ^ Module.finrank ℚ F *
          height F (p + 2) (b.val *ᵥ rational F (p + 2) (padRational r)) := hk'
    _ = (((p + 2 : ℕ) : ℝ) * B) ^ Module.finrank ℚ F * rationalHeight F 2 b₂ r := by
        rw [hbv, height_padVector]
        rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left hH
        (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hB) _)

/-! ## Reduction by induction on the rank -/

variable (F)

theorem hasReduction_zero : HasReduction F 0 1 1 := by
  intro g
  refine ⟨1, 1, g, by rw [map_one, mul_one, one_mul], isBoundedUnimodular_one F 0,
    fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩

theorem hasReduction_one : HasReduction F 1 1 1 := by
  intro g
  refine ⟨1, 1, g, by rw [map_one, mul_one, one_mul], isBoundedUnimodular_one F 1,
    fun i j h => absurd h (by rw [Subsingleton.elim i j]; exact lt_irrefl j),
    fun _ => Matrix.GeneralLinearGroup.det g, fun i => ?_, fun i j h => ?_⟩
  · rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique, Subsingleton.elim i default]
  · have := j.isLt
    omega

section Step

variable {F}

/-- The triangular factor of the inductive step: `diag(1, k'⁻¹) (k⁻¹ h) diag(1, γ')`. -/
def stepTriangular {p : ℕ} (h : AdelicGL F (p + 2)) (k' : AdelicGL F (p + 1))
    (γ' : RationalGL F (p + 1)) : AdelicGL F (p + 2) :=
  extendGL (Adeles F) (p + 1) k'⁻¹ * leadingRemainder h *
    extendGL (Adeles F) (p + 1) (AdelicGL.rational F (p + 1) γ')

/-- The bounded factor of the inductive step: `k diag(1, k')`. -/
def stepBounded {p : ℕ} (h : AdelicGL F (p + 2)) (k' : AdelicGL F (p + 1)) :
    AdelicGL F (p + 2) :=
  leadingFactor h * extendGL (Adeles F) (p + 1) k'

theorem rational_extendGL {p : ℕ} (γ' : RationalGL F p) :
    AdelicGL.rational F (p + 1) (extendGL F p γ') =
      extendGL (Adeles F) p (AdelicGL.rational F p γ') := by
  apply Units.ext
  change (extendMatrix γ'.val).map (algebraMap F (Adeles F)) =
    extendMatrix (γ'.val.map (algebraMap F (Adeles F)))
  exact map_extendMatrix _ _

theorem stepBounded_mul_stepTriangular {p : ℕ} (h : AdelicGL F (p + 2))
    (k' : AdelicGL F (p + 1)) (γ' : RationalGL F (p + 1)) :
    stepBounded h k' * stepTriangular h k' γ' =
      h * AdelicGL.rational F (p + 2) (extendGL F (p + 1) γ') := by
  rw [stepBounded, stepTriangular, rational_extendGL, map_inv, mul_assoc, mul_assoc,
    mul_inv_cancel_left, ← mul_assoc, leadingFactor_mul_leadingRemainder]

theorem stepTriangular_mulVec_first {p : ℕ} (h : AdelicGL F (p + 2))
    (k' : AdelicGL F (p + 1)) (γ' : RationalGL F (p + 1)) :
    (stepTriangular h k' γ').val *ᵥ Pi.single 0 1 =
      (leadingContent h).val • (Pi.single 0 1 : Vector F (p + 2)) := by
  rw [stepTriangular, Units.val_mul, Units.val_mul, extendGL_val, extendGL_val,
    ← Matrix.mulVec_mulVec, extendMatrix_mulVec_single, ← Matrix.mulVec_mulVec,
    leadingRemainder_mulVec_first, Matrix.mulVec_smul, extendMatrix_mulVec_single]

theorem stepTriangular_zero_zero {p : ℕ} (h : AdelicGL F (p + 2))
    (k' : AdelicGL F (p + 1)) (γ' : RationalGL F (p + 1)) :
    stepTriangular h k' γ' 0 0 = (leadingContent h).val := by
  have h' := congrFun (stepTriangular_mulVec_first h k' γ') 0
  rw [Matrix.mulVec_single_one] at h'
  simpa using h'

theorem stepTriangular_succ_zero {p : ℕ} (h : AdelicGL F (p + 2))
    (k' : AdelicGL F (p + 1)) (γ' : RationalGL F (p + 1)) (i : Fin (p + 1)) :
    stepTriangular h k' γ' i.succ 0 = 0 := by
  have h' := congrFun (stepTriangular_mulVec_first h k' γ') i.succ
  rw [Matrix.mulVec_single_one] at h'
  simpa [Fin.succ_ne_zero] using h'

theorem lowerBlock_stepTriangular {p : ℕ} (h : AdelicGL F (p + 2))
    {k' b' : AdelicGL F (p + 1)} {γ' : RationalGL F (p + 1)}
    (hfac' : lowerRemainder h * AdelicGL.rational F (p + 1) γ' = k' * b') :
    lowerBlock (stepTriangular h k' γ').val = b'.val := by
  have hb' : b'.val = (k'⁻¹).val * (lowerRemainder h).val *
      (AdelicGL.rational F (p + 1) γ').val := by
    rw [mul_assoc, ← Units.val_mul, hfac', ← Units.val_mul, inv_mul_cancel_left]
  have hA : ∀ i : Fin (p + 1), extendMatrix (k'⁻¹).val i.succ 0 = 0 :=
    extendMatrix_succ_zero _
  have hAB : ∀ i : Fin (p + 1),
      (extendMatrix (k'⁻¹).val * (leadingRemainder h).val) i.succ 0 = 0 :=
    mul_succ_zero _ _ hA (leadingRemainder_succ_zero h)
  rw [stepTriangular, Units.val_mul, Units.val_mul, extendGL_val, extendGL_val,
    lowerBlock_mul _ _ hAB, lowerBlock_mul _ _ hA, lowerBlock_extendMatrix,
    lowerBlock_extendMatrix, ← lowerRemainder_val, hb']

theorem isUpperTriangular_stepTriangular {p : ℕ} (h : AdelicGL F (p + 2))
    {k' b' : AdelicGL F (p + 1)} {γ' : RationalGL F (p + 1)}
    (hfac' : lowerRemainder h * AdelicGL.rational F (p + 1) γ' = k' * b')
    (hb' : b'.val.IsUpperTriangular) : (stepTriangular h k' γ').val.IsUpperTriangular := by
  intro i j hij
  cases i using Fin.cases with
  | zero => exact absurd hij (Fin.not_lt_zero _)
  | succ i =>
    cases j using Fin.cases with
    | zero => exact stepTriangular_succ_zero h k' γ' i
    | succ j =>
      have hblock := congrFun (congrFun (lowerBlock_stepTriangular h hfac') i) j
      change stepTriangular h k' γ' i.succ j.succ = 0
      rw [show stepTriangular h k' γ' i.succ j.succ = b' i j from hblock]
      exact hb' (Fin.succ_lt_succ_iff.mp hij)

/-- **The first diagonal ratio.** If `h` has a first column of minimal height, the
first two diagonal ideles of the triangular factor satisfy `|t₀| ≤ C'² |t₁|`. -/
theorem first_ratio_le {p : ℕ} {B C : ℝ} (hB : 0 ≤ B)
    (hherm : ∀ g : AdelicGL F 2, ∃ r : Fin 2 → F, r ≠ 0 ∧
      rationalHeight F 2 g r ≤
        C * Real.sqrt ((IdeleAbsoluteValue.full F (Matrix.GeneralLinearGroup.det g) : ℝ≥0) : ℝ))
    (h : AdelicGL F (p + 2))
    (hmin : ∀ v : Fin (p + 2) → F, v ≠ 0 →
      rationalHeight F (p + 2) h (firstVector F (p + 2) (by omega)) ≤
        rationalHeight F (p + 2) h v)
    {k' b' : AdelicGL F (p + 1)} {γ' : RationalGL F (p + 1)}
    (hfac' : lowerRemainder h * AdelicGL.rational F (p + 1) γ' = k' * b')
    (hk : IsBoundedUnimodular F (p + 2) B (stepBounded h k'))
    (hb' : b'.val.IsUpperTriangular) {t₁ : Ideles F} (h11 : b' 0 0 = t₁.val) :
    ((IdeleAbsoluteValue.full F (leadingContent h) : ℝ≥0) : ℝ) ≤
      ((((p + 2 : ℕ) : ℝ) * B) ^ Module.finrank ℚ F * C) ^ 2 *
        ((IdeleAbsoluteValue.full F t₁ : ℝ≥0) : ℝ) := by
  have h11' : stepTriangular h k' γ' 1 1 = t₁.val := by
    have hblock := congrFun (congrFun (lowerBlock_stepTriangular h hfac') 0) 0
    rw [← Fin.succ_zero_eq_one]
    exact hblock.trans h11
  obtain ⟨v, hv, hle⟩ := exists_rationalHeight_le_of_triangular hB hherm hk
    (isUpperTriangular_stepTriangular h hfac' hb') (stepTriangular_zero_zero h k' γ') h11'
  have hmin' : rationalHeight F (p + 2) h (firstVector F (p + 2) (by omega)) ≤
      rationalHeight F (p + 2) (stepBounded h k' * stepTriangular h k' γ') v := by
    rw [stepBounded_mul_stepTriangular, rationalHeight_mul_rational]
    exact hmin _ (rational_mulVec_ne_zero F (p + 2) _ hv)
  rw [rationalHeight_leading] at hmin'
  set C' : ℝ := (((p + 2 : ℕ) : ℝ) * B) ^ Module.finrank ℚ F * C with hC'
  set a : ℝ := ((IdeleAbsoluteValue.full F (leadingContent h) : ℝ≥0) : ℝ)
  set d : ℝ := ((IdeleAbsoluteValue.full F t₁ : ℝ≥0) : ℝ)
  have ha : 0 < a := IdeleAbsoluteValue.full_pos F _
  have hd : 0 < d := IdeleAbsoluteValue.full_pos F _
  have hab : a ≤ C' * Real.sqrt (a * d) := by
    rw [hC', mul_assoc]
    exact hmin'.trans hle
  have hsq : a ^ 2 ≤ C' ^ 2 * (a * d) := by
    have h2 := pow_le_pow_left₀ ha.le hab 2
    rwa [mul_pow, Real.sq_sqrt (mul_nonneg ha.le hd.le)] at h2
  nlinarith

end Step

/-- **The inductive step.** Reduction in rank `p + 1` gives reduction in rank
`p + 2`. -/
theorem hasReduction_succ {p : ℕ} {c B : ℝ} (hc : 0 < c) (hB : 1 ≤ B)
    (hred : HasReduction F (p + 1) c B) :
    ∃ c' B' : ℝ, 0 < c' ∧ 1 ≤ B' ∧ HasReduction F (p + 2) c' B' := by
  obtain ⟨C, hC, hherm⟩ := exists_rationalHeight_le_sqrt_det F
  have hB'1 : 1 ≤ ((p + 2 : ℕ) : ℝ) * B := by
    have : (1 : ℝ) ≤ ((p + 2 : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ p + 2 := by omega
      exact_mod_cast this
    nlinarith
  refine ⟨max c (((((p + 2 : ℕ) : ℝ) * (((p + 2 : ℕ) : ℝ) * B)) ^ Module.finrank ℚ F * C) ^ 2),
    ((p + 2 : ℕ) : ℝ) * B, lt_max_of_lt_left hc, hB'1, fun g => ?_⟩
  have hn : 0 < p + 2 := by omega
  obtain ⟨γ', k', b', hfac', hk', hb'tri, t', ht'diag, ht'ratio⟩ :=
    hred (lowerRemainder (minimumAdaptedMatrix F (p + 2) g hn))
  have hk : IsBoundedUnimodular F (p + 2) (((p + 2 : ℕ) : ℝ) * B)
      (stepBounded (minimumAdaptedMatrix F (p + 2) g hn) k') :=
    (isBoundedUnimodular_leadingFactor _).mul_extendGL F hk' hB
  have hlow := lowerBlock_stepTriangular (minimumAdaptedMatrix F (p + 2) g hn) hfac'
  refine ⟨minimumBasisChange F (p + 2) g hn * extendGL F (p + 1) γ',
    stepBounded (minimumAdaptedMatrix F (p + 2) g hn) k',
    stepTriangular (minimumAdaptedMatrix F (p + 2) g hn) k' γ', ?_, hk,
    isUpperTriangular_stepTriangular _ hfac' hb'tri,
    Matrix.vecCons (leadingContent (minimumAdaptedMatrix F (p + 2) g hn)) t', fun i => ?_,
    fun i j hij => ?_⟩
  · rw [stepBounded_mul_stepTriangular, map_mul, ← mul_assoc]
    rfl
  · cases i using Fin.cases with
    | zero => simpa using stepTriangular_zero_zero _ k' γ'
    | succ i =>
      rw [Matrix.cons_val_succ, ← ht'diag i]
      exact congrFun (congrFun hlow i) i
  · cases j using Fin.cases with
    | zero => simp at hij
    | succ j =>
      cases i using Fin.cases with
      | zero =>
        have hj : j = 0 := Fin.ext (by simpa using hij.symm)
        subst hj
        rw [Matrix.cons_val_zero, Matrix.cons_val_succ]
        exact (first_ratio_le (zero_le_one.trans hB'1) hherm _
          (minimumAdaptedMatrix_first_min F (p + 2) g hn) hfac' hk hb'tri (ht'diag 0)).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (IdeleAbsoluteValue.full_pos F _).le)
      | succ i =>
        rw [Matrix.cons_val_succ, Matrix.cons_val_succ]
        have hij' : i.val + 1 = j.val := by simpa using hij
        exact (ht'ratio i j hij').trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (IdeleAbsoluteValue.full_pos F _).le)

/-- Reduction holds in every rank. -/
theorem exists_hasReduction : ∀ n : ℕ, ∃ c B : ℝ, 0 < c ∧ 1 ≤ B ∧ HasReduction F n c B
  | 0 => ⟨1, 1, one_pos, le_rfl, hasReduction_zero F⟩
  | 1 => ⟨1, 1, one_pos, le_rfl, hasReduction_one F⟩
  | p + 2 => by
    obtain ⟨c, B, hc, hB, h⟩ := exists_hasReduction (p + 1)
    exact hasReduction_succ F hc hB h

/-- **Reduction theory for the actual adelic `GL(n)`.** For every number field `F`
and every `n` there are constants `c > 0` and `B ≥ 1` such that every actual adelic
matrix `g`, after right multiplication by a rational invertible matrix `γ`, is a
product `k b` of an actual adelic matrix `k` with integral finite entries, infinite
entries of norm at most `B` and determinant of local norm one at every place, and
an actual upper triangular adelic matrix `b` with diagonal ideles `t i` satisfying
`|t i| ≤ c |t (i + 1)|`. -/
theorem exists_reduction_GL (n : ℕ) :
    ∃ c B : ℝ, 0 < c ∧ 1 ≤ B ∧ ∀ g : AdelicGL F n, ∃ (γ : RationalGL F n)
      (k b : AdelicGL F n), g * AdelicGL.rational F n γ = k * b ∧
        IsBoundedUnimodular F n B k ∧ IsReducedTriangular F n c b :=
  exists_hasReduction F n

end Langlands.Global.PrimitiveAdelicHeight
