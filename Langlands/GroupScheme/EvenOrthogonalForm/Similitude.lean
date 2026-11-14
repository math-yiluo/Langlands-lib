import Langlands.GroupScheme.OrthogonalMatrix.Subgroups
import Langlands.GroupScheme.Quaternionic.Involution

/-! # The orthogonal adjoint involution and similitudes of the split hyperbolic form

For the split quadratic form on `l ⊕ l` with Gram matrix `Q = [[0, 1], [0, 0]]` and polar
matrix `J = [[0, 1], [1, 0]]`, this module introduces

* the adjoint involution `τ₀ x = J xᵀ J` of the polar form (`orthogonalInvolution`);
* the projection `p = [[1, 0], [0, 0]]` with `p J = Q` and `p + τ₀ p = 1`;
* the description of the alternating elements `{y - τ₀ y}` as the matrices `M` with `M J`
  alternating, and the orthogonality criterion `x p τ₀(x) - p ∈ {y - τ₀ y}`;
* similitudes `g` (`g Q gᵀ - μ Q` alternating): conjugation by `g` commutes with `τ₀` and
  moves `p` only by an alternating element;
* a matrix commuting with all upper and lower unipotent orthogonal matrices is a scalar,
  when the index type has at least three elements.
-/

noncomputable section

universe u

open Matrix
open scoped Matrix

namespace Langlands.GroupScheme.EvenOrthogonalForm

open OrthogonalMatrix Quaternionic

section Involution

variable (R : Type u) [CommRing R] (l : Type) [Fintype l] [DecidableEq l]

/-- The involution `x ↦ J xᵀ J` adjoint to the polar form `J = [[0, 1], [1, 0]]` of the split
quadratic form. -/
def orthogonalInvolution : FirstKindInvolution R (Matrix (l ⊕ l) (l ⊕ l) R) where
  toLinearMap :=
    { toFun := fun x => polarMatrix l R * xᵀ * polarMatrix l R
      map_add' := fun x y => by simp [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r x => by simp [Matrix.transpose_smul] }
  map_one' := by
    change polarMatrix l R * (1 : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ * polarMatrix l R = 1
    simp
  map_mul' := fun x y => by
    change polarMatrix l R * (x * y)ᵀ * polarMatrix l R =
      (polarMatrix l R * yᵀ * polarMatrix l R) * (polarMatrix l R * xᵀ * polarMatrix l R)
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (polarMatrix l R) (polarMatrix l R), polarMatrix_mul_self,
      Matrix.one_mul]
  involutive' := fun x => by
    change polarMatrix l R * (polarMatrix l R * xᵀ * polarMatrix l R)ᵀ * polarMatrix l R = x
    simp only [Matrix.transpose_mul, polarMatrix_transpose, Matrix.transpose_transpose,
      Matrix.mul_assoc, polarMatrix_mul_self, Matrix.mul_one]
    rw [← Matrix.mul_assoc, polarMatrix_mul_self, Matrix.one_mul]

variable {R l}

theorem orthogonalInvolution_apply (x : Matrix (l ⊕ l) (l ⊕ l) R) :
    orthogonalInvolution R l x = polarMatrix l R * xᵀ * polarMatrix l R :=
  rfl

theorem orthogonalInvolution_mul_polar (x : Matrix (l ⊕ l) (l ⊕ l) R) :
    orthogonalInvolution R l x * polarMatrix l R = polarMatrix l R * xᵀ := by
  rw [orthogonalInvolution_apply, Matrix.mul_assoc, polarMatrix_mul_self, Matrix.mul_one]

theorem orthogonalInvolution_map {S : Type u} [CommRing S] (f : R →+* S)
    (x : Matrix (l ⊕ l) (l ⊕ l) R) :
    (orthogonalInvolution R l x).map f = orthogonalInvolution S l (x.map f) := by
  rw [orthogonalInvolution_apply, orthogonalInvolution_apply, Matrix.map_mul, Matrix.map_mul,
    polarMatrix_map, Matrix.transpose_map]

/-- The alternating elements `y - τ₀ y` are the matrices `M` with `M J` alternating. -/
theorem mem_alternatingSubspace_iff (M : Matrix (l ⊕ l) (l ⊕ l) R) :
    M ∈ (orthogonalInvolution R l).alternatingSubspace ↔ IsAlt (M * polarMatrix l R) := by
  rw [FirstKindInvolution.mem_alternatingSubspace]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y * polarMatrix l R, ?_⟩
    rw [Matrix.sub_mul, orthogonalInvolution_mul_polar, Matrix.transpose_mul,
      polarMatrix_transpose]
  · rintro ⟨U, hU⟩
    refine ⟨U * polarMatrix l R, ?_⟩
    have h : M = (U - Uᵀ) * polarMatrix l R := by
      rw [← hU, Matrix.mul_assoc, polarMatrix_mul_self, Matrix.mul_one]
    rw [orthogonalInvolution_apply, h, Matrix.transpose_mul, polarMatrix_transpose,
      Matrix.sub_mul, ← Matrix.mul_assoc (polarMatrix l R) (polarMatrix l R), polarMatrix_mul_self,
      Matrix.one_mul]

variable (R l) in
/-- The projection `p = [[1, 0], [0, 0]]`, with `p J = Q`. -/
def leftProjection : Matrix (l ⊕ l) (l ⊕ l) R :=
  Matrix.fromBlocks 1 0 0 0

theorem leftProjection_mul_polar :
    leftProjection R l * polarMatrix l R = formMatrix l R := by
  simp [leftProjection, polarMatrix, formMatrix, Matrix.fromBlocks_multiply]

omit [Fintype l] in
theorem leftProjection_map {S : Type u} [CommRing S] (f : R →+* S) :
    (leftProjection R l).map f = leftProjection S l := by
  simp [leftProjection, Matrix.fromBlocks_map]

theorem leftProjection_add_orthogonalInvolution :
    leftProjection R l + orthogonalInvolution R l (leftProjection R l) = 1 := by
  simp [orthogonalInvolution_apply, leftProjection, polarMatrix, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_add, ← Matrix.fromBlocks_one]

/-- The defect `x p τ₀(x) - p` times `J` is the orthogonal defect `x Q xᵀ - Q`. -/
theorem projection_defect_mul_polar (x : Matrix (l ⊕ l) (l ⊕ l) R) :
    (x * leftProjection R l * orthogonalInvolution R l x - leftProjection R l) *
        polarMatrix l R = OrthogonalMatrix.defect x := by
  rw [Matrix.sub_mul, Matrix.mul_assoc, orthogonalInvolution_mul_polar, leftProjection_mul_polar,
    ← Matrix.mul_assoc, Matrix.mul_assoc x, leftProjection_mul_polar, OrthogonalMatrix.defect]

/-- A matrix is orthogonal exactly when `x p τ₀(x) - p` is alternating for `τ₀`. -/
theorem mem_orthogonalGroup_iff_projection (x : Matrix (l ⊕ l) (l ⊕ l) R) :
    x ∈ OrthogonalMatrix.orthogonalGroup l R ↔
      x * leftProjection R l * orthogonalInvolution R l x - leftProjection R l ∈
        (orthogonalInvolution R l).alternatingSubspace := by
  rw [mem_alternatingSubspace_iff, projection_defect_mul_polar,
    OrthogonalMatrix.mem_orthogonalGroup_iff]

end Involution

section Similitude

variable {R : Type u} [CommRing R] {l : Type} [Fintype l] [DecidableEq l]

/-- A similitude multiplies the polar form by its multiplier. -/
theorem similitude_polar {g : Matrix (l ⊕ l) (l ⊕ l) R} {μ : R}
    (hg : IsAlt (g * formMatrix l R * gᵀ - μ • formMatrix l R)) :
    g * polarMatrix l R * gᵀ = μ • polarMatrix l R := by
  have h := ((isAlt_iff _).1 hg).1
  rw [← formMatrix_add_transpose]
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_smul] at h
  rw [Matrix.mul_add, Matrix.add_mul, smul_add]
  rw [← sub_eq_zero, ← h]
  simp only [Matrix.mul_assoc]
  abel

variable {g g' : Matrix (l ⊕ l) (l ⊕ l) R} {μ μ' : R}

/-- For a similitude `g` with inverse `g'` and multiplier `μ`, `J gᵀ = μ g' J`. -/
theorem polar_mul_transpose_of_similitude (hg'g : g' * g = 1)
    (hg : g * polarMatrix l R * gᵀ = μ • polarMatrix l R) :
    polarMatrix l R * gᵀ = μ • (g' * polarMatrix l R) := by
  have h := congrArg (fun M => g' * M) hg
  simp only [Matrix.mul_smul] at h
  rw [← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hg'g, Matrix.one_mul]

/-- For a similitude `g` with inverse `g'` and multiplier `μ`, `g J = μ J g'ᵀ`. -/
theorem mul_polar_of_similitude (hg'g : g' * g = 1)
    (hg : g * polarMatrix l R * gᵀ = μ • polarMatrix l R) :
    g * polarMatrix l R = μ • (polarMatrix l R * g'ᵀ) := by
  have h := congrArg Matrix.transpose (polar_mul_transpose_of_similitude hg'g hg)
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose, polarMatrix_transpose,
    Matrix.transpose_smul, Matrix.transpose_mul, polarMatrix_transpose] at h

/-- For a similitude `g` with inverse `g'` and multiplier `μ` with inverse `μ'`,
`g'ᵀ J = μ' J g`. -/
theorem transpose_inv_mul_polar_of_similitude (hg'g : g' * g = 1) (hμ : μ' * μ = 1)
    (hg : g * polarMatrix l R * gᵀ = μ • polarMatrix l R) :
    g'ᵀ * polarMatrix l R = μ' • (polarMatrix l R * g) := by
  have h := mul_polar_of_similitude hg'g hg
  have h2 : polarMatrix l R * g * polarMatrix l R = μ • g'ᵀ := by
    rw [Matrix.mul_assoc, h, Matrix.mul_smul, ← Matrix.mul_assoc, polarMatrix_mul_self,
      Matrix.one_mul]
  have h3 : μ' • (polarMatrix l R * g * polarMatrix l R) = g'ᵀ := by
    rw [h2, smul_smul, hμ, one_smul]
  rw [← h3, Matrix.smul_mul, Matrix.mul_assoc, polarMatrix_mul_self, Matrix.mul_one]

/-- Conjugation by a similitude commutes with the orthogonal involution. -/
theorem orthogonalInvolution_conj_of_similitude (hg'g : g' * g = 1)
    (hμ : μ' * μ = 1) (hg : g * polarMatrix l R * gᵀ = μ • polarMatrix l R)
    (x : Matrix (l ⊕ l) (l ⊕ l) R) :
    orthogonalInvolution R l (g' * x * g) = g' * orthogonalInvolution R l x * g := by
  have h1 := polar_mul_transpose_of_similitude hg'g hg
  have h2 := transpose_inv_mul_polar_of_similitude hg'g hμ hg
  rw [orthogonalInvolution_apply, orthogonalInvolution_apply, Matrix.transpose_mul,
    Matrix.transpose_mul]
  calc polarMatrix l R * (gᵀ * (xᵀ * g'ᵀ)) * polarMatrix l R
      = (polarMatrix l R * gᵀ) * xᵀ * (g'ᵀ * polarMatrix l R) := by
        simp only [Matrix.mul_assoc]
    _ = g' * (polarMatrix l R * xᵀ * polarMatrix l R) * g := by
        rw [h1, h2, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm, hμ,
          one_smul]
        simp only [Matrix.mul_assoc]

/-- Conjugation by a similitude moves `p` by an alternating element. -/
theorem conj_leftProjection_sub_mem (hg'g : g' * g = 1)
    (hg : IsAlt (g * formMatrix l R * gᵀ - μ • formMatrix l R)) :
    g' * leftProjection R l * g - leftProjection R l ∈
      (orthogonalInvolution R l).alternatingSubspace := by
  have hJ := similitude_polar hg
  have h1 := mul_polar_of_similitude hg'g hJ
  rw [mem_alternatingSubspace_iff]
  have hT : gᵀ * g'ᵀ = 1 := by rw [← Matrix.transpose_mul, hg'g, Matrix.transpose_one]
  have key : (g' * leftProjection R l * g - leftProjection R l) * polarMatrix l R =
      -(g' * (g * formMatrix l R * gᵀ - μ • formMatrix l R) * g'ᵀ) := by
    rw [Matrix.sub_mul, leftProjection_mul_polar, Matrix.mul_assoc, h1, Matrix.mul_smul,
      ← Matrix.mul_assoc (g' * leftProjection R l),
      Matrix.mul_assoc g' (leftProjection R l) (polarMatrix l R), leftProjection_mul_polar,
      Matrix.mul_sub,
      Matrix.sub_mul]
    have e1 : g' * (g * formMatrix l R * gᵀ) * g'ᵀ = formMatrix l R := by
      calc g' * (g * formMatrix l R * gᵀ) * g'ᵀ
          = (g' * g) * formMatrix l R * (gᵀ * g'ᵀ) := by simp only [Matrix.mul_assoc]
        _ = formMatrix l R := by rw [hg'g, hT, Matrix.one_mul, Matrix.mul_one]
    rw [e1, Matrix.mul_smul, Matrix.smul_mul, neg_sub]
  rw [key]
  exact (hg.conj g').neg

/-! ### Matrices commuting with the unipotent orthogonal matrices -/

/-- The alternating matrix `E_ij - E_ji`. -/
def altBasis (i j : l) : Matrix l l R :=
  Matrix.single i j 1 - (Matrix.single i j 1)ᵀ

omit [Fintype l] in
theorem isAlt_altBasis (i j : l) : IsAlt (altBasis (R := R) i j) :=
  ⟨Matrix.single i j 1, rfl⟩

omit [Fintype l] in
theorem altBasis_eq (i j : l) :
    altBasis (R := R) i j = Matrix.single i j 1 - Matrix.single j i 1 := by
  rw [altBasis, Matrix.transpose_single]

theorem single_one_mul_apply (i j a b : l) (M : Matrix l l R) :
    (Matrix.single i j (1 : R) * M) a b = if a = i then M j b else 0 := by
  by_cases h : a = i
  · subst h
    simp
  · simp [h]

theorem mul_single_one_apply (i j a b : l) (M : Matrix l l R) :
    (M * Matrix.single i j (1 : R)) a b = if b = j then M a i else 0 := by
  by_cases h : b = j
  · subst h
    simp
  · simp [h]

theorem altBasis_mul_apply (i j a b : l) (M : Matrix l l R) :
    (altBasis (R := R) i j * M) a b = (if a = i then M j b else 0) - (if a = j then M i b else 0) := by
  rw [altBasis_eq, Matrix.sub_mul, Matrix.sub_apply, single_one_mul_apply,
    single_one_mul_apply]

theorem mul_altBasis_apply (i j a b : l) (M : Matrix l l R) :
    (M * altBasis (R := R) i j) a b = (if b = j then M a i else 0) - (if b = i then M a j else 0) := by
  rw [altBasis_eq, Matrix.mul_sub, Matrix.sub_apply, mul_single_one_apply,
    mul_single_one_apply]

/-- A matrix `c` with `Y c = 0` for all `Y = E_ij - E_ji` vanishes (two indices suffice). -/
theorem eq_zero_of_altBasis_mul (hl : ∀ k : l, ∃ i, i ≠ k) (c : Matrix l l R)
    (hc : ∀ i j, i ≠ j → altBasis i j * c = 0) : c = 0 := by
  ext j k
  obtain ⟨i, hi⟩ := hl j
  have h := congrFun (congrFun (hc i j hi) i) k
  rw [altBasis_mul_apply, Matrix.zero_apply] at h
  simpa [hi] using h

/-- If `a Y = Y d` for all `Y = E_ij - E_ji` and the index type has at least three elements,
then `a = d` is a scalar matrix. -/
theorem eq_scalar_of_mul_altBasis (hl : ∀ i k : l, ∃ j, j ≠ i ∧ j ≠ k) (i₀ : l)
    (a d : Matrix l l R) (h : ∀ i j, i ≠ j → a * altBasis i j = altBasis i j * d) :
    a = a i₀ i₀ • 1 ∧ d = a i₀ i₀ • 1 := by
  -- the entry `(k, j)` of `a Y = Y d` for `Y = E_ij - E_ji`
  have hkj : ∀ i j k, i ≠ j →
      a k i = (if k = i then d j j else 0) - (if k = j then d i j else 0) := by
    intro i j k hij
    have e := congrFun (congrFun (h i j hij) k) j
    rw [mul_altBasis_apply, altBasis_mul_apply] at e
    simpa [Ne.symm hij] using e
  -- the entry `(i, k)` for `k ≠ i, j`
  have hik : ∀ i j k, i ≠ j → k ≠ i → k ≠ j → d j k = 0 := by
    intro i j k hij hki hkj'
    have e := congrFun (congrFun (h i j hij) i) k
    rw [mul_altBasis_apply, altBasis_mul_apply] at e
    simpa [hij, hki, hkj'] using e.symm
  have ha_off : ∀ k i, k ≠ i → a k i = 0 := by
    intro k i hki
    obtain ⟨j, hji, hjk⟩ := hl i k
    rw [hkj i j k (Ne.symm hji)]
    simp [hki, Ne.symm hjk]
  have hd_off : ∀ j k, j ≠ k → d j k = 0 := by
    intro j k hjk
    obtain ⟨i, hij, hik'⟩ := hl j k
    exact hik i j k hij (Ne.symm hik') (Ne.symm hjk)
  have had : ∀ i j, i ≠ j → a i i = d j j := by
    intro i j hij
    rw [hkj i j i hij]
    simp [hij]
  have ha_diag : ∀ i, a i i = a i₀ i₀ := by
    intro i
    obtain ⟨j, hji, hji₀⟩ := hl i i₀
    rw [had i j (Ne.symm hji), had i₀ j (Ne.symm hji₀)]
  have hd_diag : ∀ j, d j j = a i₀ i₀ := by
    intro j
    obtain ⟨i, hij, -⟩ := hl j j
    rw [← had i j hij, ha_diag]
  constructor
  · ext k i
    rw [Matrix.smul_apply, Matrix.one_apply]
    by_cases hki : k = i
    · subst hki
      simp [ha_diag]
    · simp [hki, ha_off k i hki]
  · ext j k
    rw [Matrix.smul_apply, Matrix.one_apply]
    by_cases hjk : j = k
    · subst hjk
      simp [hd_diag]
    · simp [hjk, hd_off j k hjk]

/-- A matrix commuting with the upper and lower unipotent matrices `[[1, Y], [0, 1]]`,
`[[1, 0], [Y, 1]]` for `Y = E_ij - E_ji` (`i ≠ j`) is a scalar matrix, when the index type has
at least three elements. -/
theorem eq_smul_one_of_commute (hl : ∀ i k : l, ∃ j, j ≠ i ∧ j ≠ k) (i₀ : l)
    (h : Matrix (l ⊕ l) (l ⊕ l) R)
    (hup : ∀ i j : l, i ≠ j →
      h * SymplecticMatrix.upper (altBasis i j) = SymplecticMatrix.upper (altBasis i j) * h)
    (hlo : ∀ i j : l, i ≠ j →
      h * SymplecticMatrix.lower (altBasis i j) = SymplecticMatrix.lower (altBasis i j) * h) :
    h = h (Sum.inl i₀) (Sum.inl i₀) • 1 := by
  have hl2 : ∀ k : l, ∃ i, i ≠ k := fun k => (hl k k).imp fun _ h => h.1
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, h = Matrix.fromBlocks a b c d :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks h).symm⟩
  have hU : ∀ i j, i ≠ j →
      altBasis i j * c = 0 ∧ a * altBasis i j = altBasis i j * d := by
    intro i j hij
    have e := hup i j hij
    rw [SymplecticMatrix.upper, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_inj] at e
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      zero_add] at e
    obtain ⟨e1, e2, -, -⟩ := e
    exact ⟨by simpa using e1.symm, add_right_cancel (e2.trans (add_comm _ _))⟩
  have hL : ∀ i j, i ≠ j →
      altBasis i j * b = 0 ∧ d * altBasis i j = altBasis i j * a := by
    intro i j hij
    have e := hlo i j hij
    rw [SymplecticMatrix.lower, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_inj] at e
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      zero_add] at e
    obtain ⟨-, -, e3, e4⟩ := e
    exact ⟨by simpa using e4.symm, add_left_cancel (e3.trans (add_comm _ _))⟩
  have hc : c = 0 := eq_zero_of_altBasis_mul hl2 c fun i j hij => (hU i j hij).1
  have hb : b = 0 := eq_zero_of_altBasis_mul hl2 b fun i j hij => (hL i j hij).1
  obtain ⟨ha, hd⟩ := eq_scalar_of_mul_altBasis hl i₀ a d fun i j hij => (hU i j hij).2
  rw [Matrix.fromBlocks_apply₁₁, hc, hb]
  conv_lhs => rw [ha, hd]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero]

end Similitude

end Langlands.GroupScheme.EvenOrthogonalForm
