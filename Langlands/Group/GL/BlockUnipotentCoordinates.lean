import Langlands.Group.GL.PadicBlocks

/-!
# Rectangular block coordinates on the block unipotent radical

An element of the published radical `B.unipotentRadical R` is determined by its
strictly upper rectangular blocks. The inverse is the actual matrix `1 + X`, with
inverse its adjugate. See the paired Markdown for the conventions and provenance.
-/

open scoped BigOperators

namespace Langlands.GeneralLinear.BlockShape

universe u

variable {n : ℕ} (B : BlockShape n)

/-- Ordered pairs of blocks `i < j`, strictly above the block diagonal. -/
abbrev UpperPair := {ij : Fin B.length × Fin B.length // ij.1 < ij.2}

/-- With at most one block there is no pair of blocks above the diagonal. -/
theorem isEmpty_upperPair (h : B.length ≤ 1) : IsEmpty B.UpperPair := by
  refine ⟨fun ij => ?_⟩
  have hij : ij.1.1.val < ij.1.2.val := ij.2
  have hj := ij.1.2.isLt
  omega

variable (R : Type u) [CommRing R]

/-- The off-diagonal coordinate space: one rectangular `n_i × n_j` matrix for every
pair of blocks `i < j`. -/
abbrev RadicalCoordinates :=
  (ij : B.UpperPair) → Matrix (Fin (B.size ij.1.1)) (Fin (B.size ij.1.2)) R

private theorem index_apply (i : Fin B.length) (a : Fin (B.size i)) :
    B.index i a = B.indexEquiv ⟨i, a⟩ := rfl

/-- The matrix `1 + X` in block coordinates: identity diagonal blocks, the blocks
of `X` above the diagonal and zero below it. -/
def sigmaRadicalMatrix (X : B.RadicalCoordinates R) : Matrix B.Index B.Index R :=
  fun x y => if x = y then 1 else if h : x.1 < y.1 then X ⟨(x.1, y.1), h⟩ x.2 y.2 else 0

private theorem sigmaRadicalMatrix_blockTriangular (X : B.RadicalCoordinates R) :
    (B.sigmaRadicalMatrix R X).BlockTriangular Sigma.fst := by
  intro x y hyx
  have hxy : x ≠ y := fun h => lt_irrefl y.1 (h ▸ hyx)
  have hlt : ¬x.1 < y.1 := not_lt.mpr hyx.le
  simp only [sigmaRadicalMatrix]
  rw [ite_eq_right hxy, dite_eq_right hlt]

private theorem det_sigmaRadicalMatrix (X : B.RadicalCoordinates R) :
    (B.sigmaRadicalMatrix R X).det = 1 := by
  rw [(B.sigmaRadicalMatrix_blockTriangular R X).det]
  refine Finset.prod_eq_one fun k _ => ?_
  have h1 : (B.sigmaRadicalMatrix R X).toSquareBlock Sigma.fst k = 1 := by
    ext x y
    rw [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.one_apply]
    have hxy : x.1.1 = y.1.1 := x.2.trans y.2.symm
    by_cases h : x = y
    · rw [ite_eq_left h, h]
      simp only [sigmaRadicalMatrix, ite_true]
    · have h' : x.1 ≠ y.1 := fun e => h (Subtype.ext e)
      have hlt : ¬x.1.1 < y.1.1 := by
        rw [hxy]
        exact lt_irrefl _
      rw [ite_eq_right h]
      simp only [sigmaRadicalMatrix]
      rw [ite_eq_right h', dite_eq_right hlt]
  rw [h1, Matrix.det_one]

/-- The invertible matrix `1 + X` in block coordinates. Its determinant is one, so
its inverse is its adjugate. -/
def sigmaRadicalUnit (X : B.RadicalCoordinates R) : Matrix.GeneralLinearGroup B.Index R where
  val := B.sigmaRadicalMatrix R X
  inv := (B.sigmaRadicalMatrix R X).adjugate
  val_inv := by rw [Matrix.mul_adjugate, B.det_sigmaRadicalMatrix R X, one_smul]
  inv_val := by rw [Matrix.adjugate_mul, B.det_sigmaRadicalMatrix R X, one_smul]

/-- The actual invertible matrix `1 + X` in the standard coordinates of `GL_n(R)`. -/
def radicalMatrix (X : B.RadicalCoordinates R) : Langlands.GeneralLinear n R :=
  reindex (R := R) B.indexEquiv (B.sigmaRadicalUnit R X)

private theorem radicalMatrix_apply_indexEquiv (X : B.RadicalCoordinates R) (x y : B.Index) :
    B.radicalMatrix R X (B.indexEquiv x) (B.indexEquiv y) = B.sigmaRadicalMatrix R X x y := by
  change Matrix.reindex B.indexEquiv B.indexEquiv (B.sigmaRadicalMatrix R X)
    (B.indexEquiv x) (B.indexEquiv y) = _
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]

/-- Above the block diagonal, `1 + X` has the entries of `X`. -/
theorem radicalMatrix_apply_upper (X : B.RadicalCoordinates R) {i j : Fin B.length}
    (hij : i < j) (a : Fin (B.size i)) (b : Fin (B.size j)) :
    B.radicalMatrix R X (B.index i a) (B.index j b) = X ⟨(i, j), hij⟩ a b := by
  rw [index_apply, index_apply, radicalMatrix_apply_indexEquiv]
  have hne : (⟨i, a⟩ : B.Index) ≠ ⟨j, b⟩ := fun h => hij.ne (congrArg Sigma.fst h)
  simp only [sigmaRadicalMatrix]
  rw [ite_eq_right hne, dite_eq_left hij]

/-- On the diagonal blocks, `1 + X` has identity blocks. -/
theorem radicalMatrix_apply_same (X : B.RadicalCoordinates R) (i : Fin B.length)
    (a b : Fin (B.size i)) :
    B.radicalMatrix R X (B.index i a) (B.index i b) = if a = b then 1 else 0 := by
  rw [index_apply, index_apply, radicalMatrix_apply_indexEquiv]
  by_cases hab : a = b
  · subst hab
    simp only [sigmaRadicalMatrix, ite_true]
  · have hne : (⟨i, a⟩ : B.Index) ≠ ⟨i, b⟩ := fun h => hab (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
    simp only [sigmaRadicalMatrix]
    rw [ite_eq_right hne, dite_eq_right (lt_irrefl i), ite_eq_right hab]

/-- Below the block diagonal, `1 + X` vanishes. -/
theorem radicalMatrix_apply_lower (X : B.RadicalCoordinates R) {i j : Fin B.length}
    (hji : j < i) (a : Fin (B.size i)) (b : Fin (B.size j)) :
    B.radicalMatrix R X (B.index i a) (B.index j b) = 0 := by
  rw [index_apply, index_apply, radicalMatrix_apply_indexEquiv]
  have hne : (⟨i, a⟩ : B.Index) ≠ ⟨j, b⟩ := fun h => hji.ne' (congrArg Sigma.fst h)
  simp only [sigmaRadicalMatrix]
  rw [ite_eq_right hne, dite_eq_right (not_lt.mpr hji.le)]

/-- The matrix `1 + X` has determinant one. -/
theorem det_radicalMatrix (X : B.RadicalCoordinates R) :
    (B.radicalMatrix R X : Matrix (Fin n) (Fin n) R).det = 1 := by
  change (Matrix.reindex B.indexEquiv B.indexEquiv (B.sigmaRadicalMatrix R X)).det = 1
  rw [Matrix.det_reindex_self, B.det_sigmaRadicalMatrix R X]

/-- The inverse of `1 + X` is its adjugate. -/
theorem radicalMatrix_inv (X : B.RadicalCoordinates R) :
    ((B.radicalMatrix R X)⁻¹ : Langlands.GeneralLinear n R).val =
      (B.radicalMatrix R X : Matrix (Fin n) (Fin n) R).adjugate :=
  Units.inv_eq_of_mul_eq_one_right (by
    rw [Matrix.mul_adjugate, B.det_radicalMatrix R X, one_smul])

/-- The matrix `1 + X` is upper block triangular. -/
theorem radicalMatrix_mem_parabolic (X : B.RadicalCoordinates R) :
    B.radicalMatrix R X ∈ B.parabolic R :=
  (B.mem_parabolic_iff R _).mpr fun _ _ a b hji => B.radicalMatrix_apply_lower R X hji a b

/-- The matrix `1 + X` lies in the published radical. -/
theorem radicalMatrix_mem_unipotentRadical (X : B.RadicalCoordinates R) :
    (⟨B.radicalMatrix R X, B.radicalMatrix_mem_parabolic R X⟩ : B.parabolic R) ∈
      B.unipotentRadical R :=
  (B.mem_unipotentRadical_iff R _).mpr fun i a b => B.radicalMatrix_apply_same R X i a b

/-- The rectangular block coordinates of the radical. The forward map reads the
strictly upper blocks; the inverse is the actual matrix `1 + X`. This is an
equivalence of types, not of groups. -/
def radicalCoordinates : B.unipotentRadical R ≃ B.RadicalCoordinates R where
  toFun u ij a b := u.val.val (B.index ij.1.1 a) (B.index ij.1.2 b)
  invFun X := ⟨⟨B.radicalMatrix R X, B.radicalMatrix_mem_parabolic R X⟩,
    B.radicalMatrix_mem_unipotentRadical R X⟩
  left_inv u := by
    have hu := (B.mem_unipotentRadical_iff R u.val).mp u.property
    have pu := (B.mem_parabolic_iff R u.val.val).mp u.val.property
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    ext x y
    obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective x
    obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective y
    rw [← index_apply, ← index_apply]
    change B.radicalMatrix R _ (B.index i a) (B.index j b) = u.val.val (B.index i a) (B.index j b)
    rcases lt_trichotomy i j with h | rfl | h
    · exact B.radicalMatrix_apply_upper R _ h a b
    · exact (B.radicalMatrix_apply_same R _ i a b).trans (hu i a b).symm
    · exact (B.radicalMatrix_apply_lower R _ h a b).trans (pu i j a b h).symm
  right_inv X := by
    funext ij
    ext a b
    exact B.radicalMatrix_apply_upper R X ij.2 a b

/-- Forward entry formula: the coordinates are the actual matrix entries. -/
@[simp] theorem radicalCoordinates_apply (u : B.unipotentRadical R) (ij : B.UpperPair)
    (a : Fin (B.size ij.1.1)) (b : Fin (B.size ij.1.2)) :
    B.radicalCoordinates R u ij a b = u.val.val (B.index ij.1.1 a) (B.index ij.1.2 b) := rfl

/-- Inverse formula: the radical element with coordinates `X` is the matrix `1 + X`. -/
@[simp] theorem radicalCoordinates_symm_apply_val (X : B.RadicalCoordinates R) :
    ((B.radicalCoordinates R).symm X).val.val = B.radicalMatrix R X := rfl

/-- Inverse entry formula above the block diagonal: the blocks of `X`. -/
theorem radicalCoordinates_symm_apply_upper (X : B.RadicalCoordinates R) {i j : Fin B.length}
    (hij : i < j) (a : Fin (B.size i)) (b : Fin (B.size j)) :
    ((B.radicalCoordinates R).symm X).val.val (B.index i a) (B.index j b) = X ⟨(i, j), hij⟩ a b :=
  B.radicalMatrix_apply_upper R X hij a b

/-- Inverse entry formula on the diagonal blocks: identity blocks. -/
theorem radicalCoordinates_symm_apply_same (X : B.RadicalCoordinates R) (i : Fin B.length)
    (a b : Fin (B.size i)) :
    ((B.radicalCoordinates R).symm X).val.val (B.index i a) (B.index i b) =
      if a = b then 1 else 0 :=
  B.radicalMatrix_apply_same R X i a b

/-- Inverse entry formula below the block diagonal: zero. -/
theorem radicalCoordinates_symm_apply_lower (X : B.RadicalCoordinates R) {i j : Fin B.length}
    (hji : j < i) (a : Fin (B.size i)) (b : Fin (B.size j)) :
    ((B.radicalCoordinates R).symm X).val.val (B.index i a) (B.index j b) = 0 :=
  B.radicalMatrix_apply_lower R X hji a b

/-- The identity has zero coordinates. -/
@[simp] theorem radicalCoordinates_one : B.radicalCoordinates R 1 = 0 := by
  funext ij
  ext a b
  change (1 : Matrix (Fin n) (Fin n) R) (B.index ij.1.1 a) (B.index ij.1.2 b) = 0
  refine Matrix.one_apply_ne fun h => ?_
  exact ij.2.ne (congrArg Sigma.fst (B.indexEquiv.injective h))

/-- The zero coordinates give the identity. -/
@[simp] theorem radicalCoordinates_symm_zero : (B.radicalCoordinates R).symm 0 = 1 := by
  rw [Equiv.symm_apply_eq, radicalCoordinates_one]

/-- With at most one block the coordinate space, hence the radical, is trivial. -/
theorem subsingleton_unipotentRadical (h : B.length ≤ 1) :
    Subsingleton (B.unipotentRadical R) := by
  have := B.isEmpty_upperPair h
  exact (B.radicalCoordinates R).subsingleton

private theorem sum_dite_zero {ι M : Type*} [Fintype ι] [AddCommMonoid M] (p : ι → Prop)
    [DecidablePred p] (f : ∀ x, p x → M) :
    ∑ x, (if h : p x then f x h else 0) = ∑ x : {x // p x}, f x x.2 := by
  rw [← Fintype.sum_subtype_add_sum_subtype p]
  rw [Finset.sum_eq_zero (s := Finset.univ) (fun (x : {x // ¬p x}) _ => dite_eq_right x.2), add_zero]
  exact Finset.sum_congr rfl fun x _ => dite_eq_left x.2

private theorem mul_apply_index (A C : Matrix (Fin n) (Fin n) R) (x y : Fin n) :
    (A * C) x y = ∑ k : Fin B.length, ∑ c : Fin (B.size k), A x (B.index k c) * C (B.index k c) y := by
  rw [Matrix.mul_apply, ← B.indexEquiv.sum_comp, Fintype.sum_sigma]
  rfl

private theorem block_product_term (u v : B.unipotentRadical R) {i j : Fin B.length}
    (hij : i < j) (a : Fin (B.size i)) (b : Fin (B.size j)) (k : Fin B.length) :
    ∑ c : Fin (B.size k),
        u.val.val (B.index i a) (B.index k c) * v.val.val (B.index k c) (B.index j b) =
      (if k = i then v.val.val (B.index i a) (B.index j b) else 0) +
        (if k = j then u.val.val (B.index i a) (B.index j b) else 0) +
        (if h : i < k ∧ k < j then
          (B.radicalCoordinates R u ⟨(i, k), h.1⟩ * B.radicalCoordinates R v ⟨(k, j), h.2⟩) a b
        else 0) := by
  have hu := (B.mem_unipotentRadical_iff R u.val).mp u.property
  have hv := (B.mem_unipotentRadical_iff R v.val).mp v.property
  have pu := (B.mem_parabolic_iff R u.val.val).mp u.val.property
  have pv := (B.mem_parabolic_iff R v.val.val).mp v.val.property
  rcases lt_trichotomy k i with hki | rfl | hik
  · rw [ite_eq_right hki.ne, ite_eq_right (hki.trans hij).ne,
      dite_eq_right fun h => (lt_asymm hki h.1).elim, add_zero, add_zero]
    exact Finset.sum_eq_zero fun c _ => by rw [pu i k a c hki, zero_mul]
  · rw [ite_eq_left rfl, ite_eq_right hij.ne, dite_eq_right fun h => (lt_irrefl _ h.1).elim, add_zero, add_zero]
    simp only [hu, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  · rcases lt_trichotomy k j with hkj | rfl | hjk
    · rw [ite_eq_right hik.ne', ite_eq_right hkj.ne, dite_eq_left ⟨hik, hkj⟩, zero_add, zero_add, Matrix.mul_apply]
      rfl
    · rw [ite_eq_right hik.ne', ite_eq_left rfl, dite_eq_right fun h => (lt_irrefl _ h.2).elim, zero_add, add_zero]
      simp only [hv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    · rw [ite_eq_right hik.ne', ite_eq_right hjk.ne', dite_eq_right fun h => (lt_asymm hjk h.2).elim,
        add_zero, add_zero]
      exact Finset.sum_eq_zero fun c _ => by rw [pv k j c b hjk, mul_zero]

/-- The triangular multiplication formula
`(u v)_ij = u_ij + v_ij + ∑_{i < k < j} u_ik v_kj`. -/
theorem radicalCoordinates_mul (u v : B.unipotentRadical R) {i j : Fin B.length}
    (hij : i < j) :
    B.radicalCoordinates R (u * v) ⟨(i, j), hij⟩ =
      B.radicalCoordinates R u ⟨(i, j), hij⟩ + B.radicalCoordinates R v ⟨(i, j), hij⟩ +
        ∑ k : {k : Fin B.length // i < k ∧ k < j},
          B.radicalCoordinates R u ⟨(i, k), k.2.1⟩ * B.radicalCoordinates R v ⟨(k, j), k.2.2⟩ := by
  ext a b
  change ((u.val.val * v.val.val : Langlands.GeneralLinear n R) : Matrix (Fin n) (Fin n) R)
    (B.index i a) (B.index j b) = _
  rw [Units.val_mul, B.mul_apply_index R,
    Finset.sum_congr rfl fun k _ => B.block_product_term R u v hij a b k]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
    ite_eq_left (Finset.mem_univ _), ite_eq_left (Finset.mem_univ _),
    sum_dite_zero (fun k => i < k ∧ k < j), add_comm (v.val.val _ _)]
  exact congrArg₂ (· + ·) rfl (Matrix.sum_apply a b _ _).symm

/-- The inverse formula `(u⁻¹)_ij = -u_ij - ∑_{i < k < j} u_ik (u⁻¹)_kj`, determining the
coordinates of `u⁻¹` by induction on `j - i`. -/
theorem radicalCoordinates_inv (u : B.unipotentRadical R) {i j : Fin B.length} (hij : i < j) :
    B.radicalCoordinates R u⁻¹ ⟨(i, j), hij⟩ =
      -B.radicalCoordinates R u ⟨(i, j), hij⟩ -
        ∑ k : {k : Fin B.length // i < k ∧ k < j},
          B.radicalCoordinates R u ⟨(i, k), k.2.1⟩ * B.radicalCoordinates R u⁻¹ ⟨(k, j), k.2.2⟩ := by
  have h := B.radicalCoordinates_mul R u u⁻¹ hij
  rw [mul_inv_cancel, radicalCoordinates_one, Pi.zero_apply] at h
  rw [eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero, h]
  abel

/-- The group law transported to the coordinates:
`(1 + X)(1 + Y)` has coordinates `X_ij + Y_ij + ∑_{i < k < j} X_ik Y_kj`. -/
theorem radicalCoordinates_symm_mul_symm (X Y : B.RadicalCoordinates R) {i j : Fin B.length}
    (hij : i < j) :
    B.radicalCoordinates R ((B.radicalCoordinates R).symm X * (B.radicalCoordinates R).symm Y)
        ⟨(i, j), hij⟩ =
      X ⟨(i, j), hij⟩ + Y ⟨(i, j), hij⟩ +
        ∑ k : {k : Fin B.length // i < k ∧ k < j}, X ⟨(i, k), k.2.1⟩ * Y ⟨(k, j), k.2.2⟩ := by
  simpa only [Equiv.apply_symm_apply] using B.radicalCoordinates_mul R
    ((B.radicalCoordinates R).symm X) ((B.radicalCoordinates R).symm Y) hij

private theorem leviEmbedding_mul_apply (m : B.Levi R) (A : Matrix (Fin n) (Fin n) R)
    (i : Fin B.length) (a : Fin (B.size i)) (y : Fin n) :
    ((B.leviEmbedding R m : Matrix (Fin n) (Fin n) R) * A) (B.index i a) y =
      ∑ c : Fin (B.size i), (m i).val a c * A (B.index i c) y := by
  rw [B.mul_apply_index R, Fintype.sum_eq_single i]
  · exact Finset.sum_congr rfl fun c _ => by rw [B.leviEmbedding_apply_same R m i a c]
  · intro k hk
    exact Finset.sum_eq_zero fun c _ => by
      rw [B.leviEmbedding_apply_ne R m a c (Ne.symm hk), zero_mul]

private theorem mul_leviEmbedding_apply (m : B.Levi R) (A : Matrix (Fin n) (Fin n) R)
    (x : Fin n) (j : Fin B.length) (b : Fin (B.size j)) :
    (A * (B.leviEmbedding R m : Matrix (Fin n) (Fin n) R)) x (B.index j b) =
      ∑ d : Fin (B.size j), A x (B.index j d) * (m j).val d b := by
  rw [B.mul_apply_index R, Fintype.sum_eq_single j]
  · exact Finset.sum_congr rfl fun d _ => by rw [B.leviEmbedding_apply_same R m j d b]
  · intro k hk
    exact Finset.sum_eq_zero fun d _ => by
      rw [B.leviEmbedding_apply_ne R m d b hk, mul_zero]

/-- The Levi action formula `(m u m⁻¹)_ij = m_i u_ij m_j⁻¹`. -/
theorem radicalCoordinates_leviAction (m : B.Levi R) (u : B.unipotentRadical R)
    (ij : B.UpperPair) :
    B.radicalCoordinates R (B.leviAction R m u) ij =
      (m ij.1.1).val * B.radicalCoordinates R u ij * ((m ij.1.2)⁻¹).val := by
  ext a b
  change ((B.leviEmbedding R m * u.val.val * (B.leviEmbedding R m)⁻¹ :
      Langlands.GeneralLinear n R) : Matrix (Fin n) (Fin n) R)
    (B.index ij.1.1 a) (B.index ij.1.2 b) = _
  rw [← map_inv (B.leviEmbedding R) m, Units.val_mul, Units.val_mul,
    B.mul_leviEmbedding_apply R, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [B.leviEmbedding_mul_apply R, Matrix.mul_apply]
  rfl

/-- The Levi action on `1 + X`, in coordinates: `X_ij ↦ m_i X_ij m_j⁻¹`. -/
theorem radicalCoordinates_leviAction_symm (m : B.Levi R) (X : B.RadicalCoordinates R)
    (ij : B.UpperPair) :
    B.radicalCoordinates R (B.leviAction R m ((B.radicalCoordinates R).symm X)) ij =
      (m ij.1.1).val * X ij * ((m ij.1.2)⁻¹).val := by
  rw [radicalCoordinates_leviAction, Equiv.apply_symm_apply]

section Topology

variable [TopologicalSpace R]

/-- Reading the coordinates is continuous for the actual radical topology. -/
theorem continuous_radicalCoordinates : Continuous (B.radicalCoordinates R) := by
  apply continuous_pi
  intro ij
  apply continuous_matrix
  intro a b
  exact (GeneralLinear.entry (B.index ij.1.1 a) (B.index ij.1.2 b)).continuous.comp
    (continuous_subtype_val.comp continuous_subtype_val)

variable [IsTopologicalRing R]

omit [IsTopologicalRing R] in
private theorem continuous_sigmaRadicalMatrix :
    Continuous (fun X : B.RadicalCoordinates R => B.sigmaRadicalMatrix R X) := by
  apply continuous_matrix
  intro x y
  by_cases hxy : x = y
  · simp only [sigmaRadicalMatrix, ite_eq_left hxy]
    exact continuous_const
  · by_cases hlt : x.1 < y.1
    · simp only [sigmaRadicalMatrix, ite_eq_right hxy, dite_eq_left hlt]
      exact (continuous_apply _).matrix_elem _ _
    · simp only [sigmaRadicalMatrix, ite_eq_right hxy, dite_eq_right hlt]
      exact continuous_const

/-- The matrix `1 + X` depends continuously on `X`; its inverse is the adjugate. -/
theorem continuous_radicalCoordinates_symm : Continuous (B.radicalCoordinates R).symm := by
  have hunit : Continuous (B.sigmaRadicalUnit R) :=
    Units.continuous_iff.mpr
      ⟨B.continuous_sigmaRadicalMatrix R, (B.continuous_sigmaRadicalMatrix R).matrix_adjugate⟩
  exact (((reindexContinuous (R := R) B.indexEquiv).continuous.comp hunit).subtype_mk _).subtype_mk _

/-- The rectangular block coordinates as a homeomorphism, for a topological
commutative ring and the actual subspace topology of the radical. -/
def radicalCoordinatesHomeomorph : B.unipotentRadical R ≃ₜ B.RadicalCoordinates R where
  toEquiv := B.radicalCoordinates R
  continuous_toFun := B.continuous_radicalCoordinates R
  continuous_invFun := B.continuous_radicalCoordinates_symm R

@[simp] theorem radicalCoordinatesHomeomorph_apply (u : B.unipotentRadical R) :
    B.radicalCoordinatesHomeomorph R u = B.radicalCoordinates R u := rfl

@[simp] theorem radicalCoordinatesHomeomorph_symm_apply (X : B.RadicalCoordinates R) :
    (B.radicalCoordinatesHomeomorph R).symm X = (B.radicalCoordinates R).symm X := rfl

end Topology

end BlockShape

end Langlands.GeneralLinear

namespace Langlands.PadicField.TopologicalData

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} {n : ℕ}

/-- The rectangular block coordinate homeomorphism for a supplied p-adic field
realization, with its exact radical topology. -/
def blockRadicalCoordinates (T : F.TopologicalData) (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    B.unipotentRadical F.Carrier ≃ₜ B.RadicalCoordinates F.Carrier := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact B.radicalCoordinatesHomeomorph F.Carrier

/-- The p-adic specialization has the same underlying equivalence. -/
theorem blockRadicalCoordinates_toEquiv (T : F.TopologicalData)
    (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    (T.blockRadicalCoordinates B).toEquiv = B.radicalCoordinates F.Carrier := rfl

end Langlands.PadicField.TopologicalData
