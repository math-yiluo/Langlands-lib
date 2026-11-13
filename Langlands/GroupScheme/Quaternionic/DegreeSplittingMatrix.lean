import Langlands.GroupScheme.Quaternionic.DegreeSplittingChart
import Langlands.GroupScheme.Quaternionic.SplittingMatrix

/-! # Splitting matrix algebras over a central simple algebra with involution, in any degree

Let `e : L ⊗[K] D ≃ₐ[L] M_ι(L)` be a matrix chart of a `K`-algebra `D` with an involution of the
first kind `σ`, for a finite index type `ι`. For a commutative `L`-algebra `R` this module
identifies `R ⊗[K] M_n(D)` with `M_{n × ι}(R)` (`matrixChartR`). It transports the
conjugate-transpose involution `σ.matrix n` to `X ↦ S̃ Xᵀ S̃⁻¹` (`matrixChartR_baseChange`),
identifies the reduced norm with the determinant (`reducedNorm_eq_det_matrixChartR`), and turns
the unitary condition `u H ᵗu^σ = H` of an antihermitian `H` into `g C gᵀ = C` for the split Gram
matrix `C` (`mul_mul_baseChange_eq_iff`), which is alternating when the symmetric elements of `σ`
have dimension `δ (δ + 1) / 2`, `δ = |ι|` (`transpose_splitGram`, `splitGram_diag`).

This generalises the Library module `Quaternionic.SplittingMatrix`, which treats `ι = Fin 2`.
-/

noncomputable section

universe u

open scoped TensorProduct
open Matrix Module

namespace Langlands.GroupScheme.Quaternionic

namespace DegreeSplitting

variable {K D : Type u} [Field K] [Ring D] [Algebra K D]
  {L : Type u} [Field L] [Algebra K L]
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (e : L ⊗[K] D ≃ₐ[L] Matrix ι ι L)
  {n : Type} [Fintype n] [DecidableEq n]

section Chart

variable (R : Type u) [CommRing R] [Algebra K R] [Algebra L R] [IsScalarTower K L R]

/-- `R ⊗[K] M_n(D) ≅ M_n(M_ι(R))`: move the scalars into the entries, then apply the chart. -/
def blockChartR : R ⊗[K] Matrix n n D ≃+* Matrix n n (Matrix ι ι R) :=
  (FiniteAlgebraUnits.MatrixPoints.coefficientEquiv (m := n) K D R).toRingEquiv.trans
    (chartR e R).mapMatrix

/-- `R ⊗[K] M_n(D) ≅ M_{n × ι}(R)`. -/
def matrixChartR : R ⊗[K] Matrix n n D ≃+* Matrix (n × ι) (n × ι) R :=
  (blockChartR e R).trans (Matrix.compRingEquiv n ι R)

theorem blockChartR_apply (x : R ⊗[K] Matrix n n D) (i j : n) :
    blockChartR e R x i j =
      chartR e R (FiniteAlgebraUnits.MatrixPoints.coefficientEquiv K D R x i j) :=
  rfl

theorem matrixChartR_eq_comp (x : R ⊗[K] Matrix n n D) :
    matrixChartR e R x = Matrix.comp n n ι ι R (blockChartR e R x) :=
  rfl

theorem matrixChartR_apply (x : R ⊗[K] Matrix n n D) (i j : n) (a b : ι) :
    matrixChartR e R x (i, a) (j, b) =
      chartR e R (FiniteAlgebraUnits.MatrixPoints.coefficientEquiv K D R x i j) a b :=
  rfl

theorem matrixChartR_tmul_apply (r : R) (M : Matrix n n D) (i j : n) (a b : ι) :
    matrixChartR e R (r ⊗ₜ[K] M) (i, a) (j, b) = r * algebraMap L R (e (1 ⊗ₜ[K] M i j) a b) := by
  rw [matrixChartR_apply, FiniteAlgebraUnits.MatrixPoints.coefficientEquiv_tmul, chartR_tmul]
  rfl

variable {R} in
/-- The matrix chart commutes with every coefficient change of `L`-algebras. -/
theorem matrixChartR_naturality {R' : Type u} [CommRing R'] [Algebra K R'] [Algebra L R']
    [IsScalarTower K L R'] (f : R →ₐ[L] R') (x : R ⊗[K] Matrix n n D) :
    matrixChartR e R' (Algebra.TensorProduct.map (f.restrictScalars K) (AlgHom.id K _) x) =
      (matrixChartR e R x).map f := by
  ext ⟨i, a⟩ ⟨j, b⟩
  rw [matrixChartR_apply, FiniteAlgebraUnits.MatrixPoints.coefficientEquiv_naturality,
    Matrix.map_apply, chartR_naturality, Matrix.map_apply, Matrix.map_apply, matrixChartR_apply]

/-- The chart over `R` of a constant element is the chart over `L` with entries mapped to `R`. -/
theorem matrixChartR_one_tmul (M : Matrix n n D) :
    matrixChartR e R (1 ⊗ₜ[K] M) = (matrixChartR e L (1 ⊗ₜ[K] M)).map (algebraMap L R) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  rw [matrixChartR_tmul_apply, Matrix.map_apply, matrixChartR_tmul_apply, one_mul, one_mul]
  rfl

end Chart

section Involution

variable (σ : FirstKindInvolution K D)

/-- The block-diagonal matrix with diagonal blocks `S`. -/
def blockInvolutionMatrix : Matrix (n × ι) (n × ι) L :=
  Matrix.comp n n ι ι L
    (Matrix.diagonal fun _ => (involutionMatrix e σ : Matrix ι ι L))

/-- The block-diagonal matrix with diagonal blocks `S⁻¹`. -/
def blockInvolutionMatrixInv : Matrix (n × ι) (n × ι) L :=
  Matrix.comp n n ι ι L
    (Matrix.diagonal fun _ => ((involutionMatrix e σ)⁻¹ : (Matrix ι ι L)ˣ))

theorem blockInvolutionMatrix_mul_inv :
    blockInvolutionMatrix e σ (n := n) * blockInvolutionMatrixInv e σ = 1 := by
  rw [blockInvolutionMatrix, blockInvolutionMatrixInv, ← Matrix.compRingEquiv_apply,
    ← Matrix.compRingEquiv_apply, ← _root_.map_mul, Matrix.diagonal_mul_diagonal, Units.mul_inv,
    Matrix.diagonal_one, _root_.map_one]

theorem blockInvolutionMatrix_inv_mul :
    blockInvolutionMatrixInv e σ (n := n) * blockInvolutionMatrix e σ = 1 := by
  rw [blockInvolutionMatrix, blockInvolutionMatrixInv, ← Matrix.compRingEquiv_apply,
    ← Matrix.compRingEquiv_apply, ← _root_.map_mul, Matrix.diagonal_mul_diagonal, Units.inv_mul,
    Matrix.diagonal_one, _root_.map_one]

omit [Fintype n] in
theorem transpose_blockInvolutionMatrix [FiniteDimensional K D]
    (hσ : finrank K σ.symmetricSubspace = Fintype.card ι * (Fintype.card ι + 1) / 2) :
    (blockInvolutionMatrix e σ (n := n))ᵀ = blockInvolutionMatrix e σ := by
  rw [blockInvolutionMatrix, Matrix.transpose_comp, Matrix.diagonal_transpose]
  congr 1
  ext i j : 1
  by_cases hij : i = j
  · subst hij
    ext a b
    simpa using congrFun (congrFun (involutionMatrix_transpose e σ hσ) a) b
  · simp [Matrix.diagonal_apply_ne _ hij]

/-- The transport of the conjugate-transpose involution of `M_n(D)`. -/
theorem matrixChartR_baseChange (R : Type u) [CommRing R] [Algebra K R] [Algebra L R]
    [IsScalarTower K L R] (x : R ⊗[K] Matrix n n D) :
    matrixChartR e R ((σ.matrix n).baseChange R x) =
      (blockInvolutionMatrix e σ).map (algebraMap L R) * (matrixChartR e R x)ᵀ *
        (blockInvolutionMatrixInv e σ).map (algebraMap L R) := by
  rw [matrixChartR_eq_comp, matrixChartR_eq_comp, blockInvolutionMatrix,
    blockInvolutionMatrixInv, ← Matrix.comp_map_map, ← Matrix.comp_map_map,
    Matrix.transpose_comp, ← Matrix.compRingEquiv_apply, ← Matrix.compRingEquiv_apply,
    ← Matrix.compRingEquiv_apply, ← Matrix.compRingEquiv_apply, ← _root_.map_mul,
    ← _root_.map_mul]
  congr 1
  ext i j : 1
  have hd : ∀ d : n → Matrix ι ι L,
      ((Matrix.diagonal d).map fun M' => M'.map (algebraMap L R)) =
        Matrix.diagonal fun m => (d m).map (algebraMap L R) :=
    fun d => Matrix.diagonal_map (by simp)
  rw [hd, hd, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.map_apply, Matrix.transpose_apply, blockChartR_apply,
    blockChartR_apply, FirstKindInvolution.coefficientEquiv_baseChange, chartR_baseChange]

end Involution

end DegreeSplitting

namespace DegreeSplitting

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  {L : Type u} [Field L] [Algebra K L]
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (e : L ⊗[K] D ≃ₐ[L] Matrix ι ι L)
  {n : Type} [Fintype n] [DecidableEq n]

section ReducedNorm

/-- The matrix chart over `L` as an `L`-algebra isomorphism. -/
def matrixChartL : L ⊗[K] Matrix n n D ≃ₐ[L] Matrix (n × ι) (n × ι) L :=
  AlgEquiv.ofRingEquiv (f := matrixChartR e L) fun c => by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    ext ⟨i, a⟩ ⟨j, b⟩
    rw [matrixChartR_tmul_apply, Matrix.algebraMap_matrix_apply]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq, ← Algebra.TensorProduct.one_def, _root_.map_one]
      by_cases hab : a = b
      · subst hab
        simp
      · simp [Matrix.one_apply_ne hab, hab]
    · rw [Matrix.one_apply_ne hij, TensorProduct.tmul_zero, _root_.map_zero]
      simp [hij]

theorem matrixChartL_apply (x : L ⊗[K] Matrix n n D) : matrixChartL e x = matrixChartR e L x :=
  rfl

/-- The splitting map of the chart `matrixChartL` is the matrix chart over every `R`. -/
theorem splittingMap_matrixChartL (R : Type u) [CommRing R] [Algebra K R] [Algebra L R]
    [IsScalarTower K L R] (x : R ⊗[K] Matrix n n D) :
    ReducedNorm.splittingMap (matrixChartL e) R x = matrixChartR e R x := by
  induction x using TensorProduct.inductionOn with
  | tmul r M =>
    rw [ReducedNorm.splittingMap_tmul]
    ext ⟨i, a⟩ ⟨j, b⟩
    rw [matrixChartR_tmul_apply, Matrix.smul_apply, Matrix.map_apply, matrixChartL_apply,
      matrixChartR_tmul_apply, one_mul, smul_eq_mul]
    rfl
  | add x y hx hy => rw [_root_.map_add, _root_.map_add, hx, hy]

variable [Algebra.IsCentral K D] [FiniteDimensional K D] [Nonempty n]

/-- The reduced norm of `M_n(D)` is the determinant in the matrix chart. -/
theorem reducedNorm_eq_det_matrixChartR (R : Type u) [CommRing R] [Algebra K R] [Algebra L R]
    [IsScalarTower K L R] (x : R ⊗[K] Matrix n n D) :
    CentralSimple.reducedNorm K (Matrix n n D) R x = (matrixChartR e R x).det := by
  rw [CentralSimple.reducedNorm_eq_det_fintype K (Matrix n n D) (matrixChartL e) R x,
    splittingMap_matrixChartL]

end ReducedNorm

section Alternating

variable (σ : FirstKindInvolution K D)

/-- The Gram matrix `C = H̃ S̃` over `L` of the split form. -/
def splitGram (H : Matrix n n D) : Matrix (n × ι) (n × ι) L :=
  matrixChartR e L (1 ⊗ₜ[K] H) * blockInvolutionMatrix e σ

theorem matrixChartL_baseChange (x : L ⊗[K] Matrix n n D) :
    matrixChartR e L ((σ.matrix n).baseChange L x) =
      blockInvolutionMatrix e σ * (matrixChartR e L x)ᵀ * blockInvolutionMatrixInv e σ := by
  simpa [Algebra.algebraMap_self] using matrixChartR_baseChange e σ L x

/-- For antihermitian `H`, when the symmetric elements of `σ` have dimension `δ (δ + 1) / 2`,
the split Gram matrix is `W - Wᵀ`. -/
theorem exists_splitGram_eq_sub [FiniteDimensional K D]
    (hσ : finrank K σ.symmetricSubspace = Fintype.card ι * (Fintype.card ι + 1) / 2)
    {H : Matrix n n D} (hH : σ.IsAntihermitian H) :
    ∃ W : Matrix (n × ι) (n × ι) L, splitGram e σ H = W - Wᵀ := by
  obtain ⟨V, rfl⟩ := FirstKindInvolution.IsAntihermitian.exists_eq_sub σ hH
  refine ⟨matrixChartR e L (1 ⊗ₜ[K] V) * blockInvolutionMatrix e σ, ?_⟩
  have h := matrixChartL_baseChange e σ (1 ⊗ₜ[K] V)
  rw [FirstKindInvolution.baseChange_tmul] at h
  rw [splitGram, TensorProduct.tmul_sub, _root_.map_sub, h, Matrix.sub_mul, Matrix.transpose_mul,
    transpose_blockInvolutionMatrix e σ hσ, Matrix.mul_assoc, blockInvolutionMatrix_inv_mul,
    Matrix.mul_one]

theorem transpose_splitGram [FiniteDimensional K D]
    (hσ : finrank K σ.symmetricSubspace = Fintype.card ι * (Fintype.card ι + 1) / 2)
    {H : Matrix n n D} (hH : σ.IsAntihermitian H) :
    (splitGram e σ H)ᵀ = -splitGram e σ H := by
  obtain ⟨W, hW⟩ := exists_splitGram_eq_sub e σ hσ hH
  rw [hW, Matrix.transpose_sub, Matrix.transpose_transpose, neg_sub]

theorem splitGram_diag [FiniteDimensional K D]
    (hσ : finrank K σ.symmetricSubspace = Fintype.card ι * (Fintype.card ι + 1) / 2)
    {H : Matrix n n D} (hH : σ.IsAntihermitian H) (p : n × ι) :
    splitGram e σ H p p = 0 := by
  obtain ⟨W, hW⟩ := exists_splitGram_eq_sub e σ hσ hH
  rw [hW, Matrix.sub_apply, Matrix.transpose_apply, sub_self]

theorem det_splitGram_ne_zero {H : Matrix n n D} (hu : IsUnit H) :
    (splitGram e σ H).det ≠ 0 := by
  have h1 : IsUnit (matrixChartR e L (1 ⊗ₜ[K] H)) :=
    (hu.map (Algebra.TensorProduct.includeRight : Matrix n n D →ₐ[K] L ⊗[K] _)).map
      (matrixChartR e L)
  have h2 : IsUnit (blockInvolutionMatrix e σ (n := n)) :=
    ⟨⟨_, _, blockInvolutionMatrix_mul_inv e σ, blockInvolutionMatrix_inv_mul e σ⟩, rfl⟩
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (h1.mul h2)).ne_zero

/-- The unitary condition `u H ᵗu^σ = H` becomes `g C gᵀ = C` for `g` the matrix chart of `u`
and `C` the split Gram matrix. -/
theorem mul_mul_baseChange_eq_iff (R : Type u) [CommRing R] [Algebra K R] [Algebra L R]
    [IsScalarTower K L R] (H : Matrix n n D) (u : R ⊗[K] Matrix n n D) :
    u * (1 ⊗ₜ[K] H) * (σ.matrix n).baseChange R u = 1 ⊗ₜ[K] H ↔
      matrixChartR e R u * (splitGram e σ H).map (algebraMap L R) * (matrixChartR e R u)ᵀ =
        (splitGram e σ H).map (algebraMap L R) := by
  set S := (blockInvolutionMatrix e σ (n := n)).map (algebraMap L R)
  set S' := (blockInvolutionMatrixInv e σ (n := n)).map (algebraMap L R)
  have hSS' : S * S' = 1 := by
    rw [← Matrix.map_mul, blockInvolutionMatrix_mul_inv, Matrix.map_one _ (_root_.map_zero _)
      (_root_.map_one _)]
  have hS'S : S' * S = 1 := by
    rw [← Matrix.map_mul, blockInvolutionMatrix_inv_mul, Matrix.map_one _ (_root_.map_zero _)
      (_root_.map_one _)]
  set g := matrixChartR e R u
  set Ht := matrixChartR e R (1 ⊗ₜ[K] H)
  have hC : (splitGram e σ H).map (algebraMap L R) = Ht * S := by
    rw [splitGram, Matrix.map_mul, ← matrixChartR_one_tmul]
  rw [← (matrixChartR (n := n) e R).injective.eq_iff, _root_.map_mul, _root_.map_mul,
    matrixChartR_baseChange, hC]
  change g * Ht * (S * gᵀ * S') = Ht ↔ g * (Ht * S) * gᵀ = Ht * S
  constructor
  · intro h
    calc g * (Ht * S) * gᵀ = g * Ht * (S * gᵀ * (S' * S)) := by
          rw [hS'S, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = g * Ht * (S * gᵀ * S') * S := by simp only [Matrix.mul_assoc]
      _ = Ht * S := by rw [h]
  · intro h
    calc g * Ht * (S * gᵀ * S') = g * (Ht * S) * gᵀ * S' := by simp only [Matrix.mul_assoc]
      _ = Ht := by rw [h, Matrix.mul_assoc, hSS', Matrix.mul_one]

end Alternating

end DegreeSplitting

end Langlands.GroupScheme.Quaternionic
