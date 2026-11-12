import Langlands.GroupScheme.Quaternionic.SplittingChart
import Langlands.GroupScheme.Quaternionic.Forms
import Langlands.GroupScheme.FiniteAlgebraMatrixPoints
import Langlands.Algebra.ReducedNormFiniteChart
import Mathlib.Data.Matrix.Composition

/-! # Splitting matrix algebras over a quaternion algebra with involution

Let `e : L ⊗[K] D ≃ₐ[L] M₂(L)` be a matrix chart of a `K`-algebra `D` with an involution of the
first kind `σ`. For a commutative `L`-algebra `R` this module identifies
`R ⊗[K] M_n(D)` with `M_{n × 2}(R)` (`matrixChartR`). It transports the conjugate-transpose
involution `σ.matrix n` to `X ↦ S̃ Xᵀ S̃⁻¹` (`matrixChartR_baseChange`), identifies the reduced
norm with the determinant (`reducedNorm_eq_det_matrixChartR`), and turns the unitary condition
`u H ᵗu^σ = H` of an antihermitian `H` into `g C gᵀ = C` for an alternating matrix `C`
(`mul_mul_baseChange_eq_iff`, `transpose_gramMatrix`, `gramMatrix_diag`).
-/

noncomputable section

universe u

open scoped TensorProduct
open Matrix Module

namespace Langlands.GroupScheme.Quaternionic

namespace FirstKindInvolution

variable {K D : Type u} [Field K] [Ring D] [Algebra K D]
  {L : Type u} [Field L] [Algebra K L]
  (e : L ⊗[K] D ≃ₐ[L] Matrix (Fin 2) (Fin 2) L)
  {n : Type} [Fintype n] [DecidableEq n]

section Chart

variable (R : Type u) [CommRing R] [Algebra K R] [Algebra L R] [IsScalarTower K L R]

/-- `R ⊗[K] M_n(D) ≅ M_n(M₂(R))`: move the scalars into the entries, then apply the chart. -/
def blockChartR : R ⊗[K] Matrix n n D ≃+* Matrix n n (Matrix (Fin 2) (Fin 2) R) :=
  (FiniteAlgebraUnits.MatrixPoints.coefficientEquiv (m := n) K D R).toRingEquiv.trans
    (chartR e R).mapMatrix

/-- `R ⊗[K] M_n(D) ≅ M_{n × 2}(R)`. -/
def matrixChartR : R ⊗[K] Matrix n n D ≃+* Matrix (n × Fin 2) (n × Fin 2) R :=
  (blockChartR e R).trans (Matrix.compRingEquiv n (Fin 2) R)

theorem blockChartR_apply (x : R ⊗[K] Matrix n n D) (i j : n) :
    blockChartR e R x i j =
      chartR e R (FiniteAlgebraUnits.MatrixPoints.coefficientEquiv K D R x i j) :=
  rfl

theorem matrixChartR_eq_comp (x : R ⊗[K] Matrix n n D) :
    matrixChartR e R x = Matrix.comp n n (Fin 2) (Fin 2) R (blockChartR e R x) :=
  rfl

theorem matrixChartR_apply (x : R ⊗[K] Matrix n n D) (i j : n) (a b : Fin 2) :
    matrixChartR e R x (i, a) (j, b) =
      chartR e R (FiniteAlgebraUnits.MatrixPoints.coefficientEquiv K D R x i j) a b :=
  rfl

theorem matrixChartR_tmul_apply (r : R) (M : Matrix n n D) (i j : n) (a b : Fin 2) :
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

/-- Scalars and the conjugate transpose: `(τ_R x) i j = σ_R (x j i)` after moving the scalars
into the entries. -/
theorem coefficientEquiv_baseChange (R : Type u) [CommRing R] [Algebra K R]
    (x : R ⊗[K] Matrix n n D) (i j : n) :
    FiniteAlgebraUnits.MatrixPoints.coefficientEquiv K D R ((σ.matrix n).baseChange R x) i j =
      σ.baseChange R (FiniteAlgebraUnits.MatrixPoints.coefficientEquiv K D R x j i) := by
  induction x using TensorProduct.inductionOn with
  | tmul r M =>
    rw [baseChange_tmul, FiniteAlgebraUnits.MatrixPoints.coefficientEquiv_tmul,
      FiniteAlgebraUnits.MatrixPoints.coefficientEquiv_tmul, baseChange_tmul, matrix_apply]
  | add x y hx hy =>
    rw [FirstKindInvolution.map_add, _root_.map_add, Matrix.add_apply, hx, hy, _root_.map_add,
      Matrix.add_apply, FirstKindInvolution.map_add]

/-- The block-diagonal matrix with diagonal blocks `S`. -/
def blockInvolutionMatrix : Matrix (n × Fin 2) (n × Fin 2) L :=
  Matrix.comp n n (Fin 2) (Fin 2) L
    (Matrix.diagonal fun _ => (σ.involutionMatrix e : Matrix (Fin 2) (Fin 2) L))

/-- The block-diagonal matrix with diagonal blocks `S⁻¹`. -/
def blockInvolutionMatrixInv : Matrix (n × Fin 2) (n × Fin 2) L :=
  Matrix.comp n n (Fin 2) (Fin 2) L
    (Matrix.diagonal fun _ => ((σ.involutionMatrix e)⁻¹ : (Matrix (Fin 2) (Fin 2) L)ˣ))

theorem blockInvolutionMatrix_mul_inv :
    σ.blockInvolutionMatrix e (n := n) * σ.blockInvolutionMatrixInv e = 1 := by
  rw [blockInvolutionMatrix, blockInvolutionMatrixInv, ← Matrix.compRingEquiv_apply,
    ← Matrix.compRingEquiv_apply, ← _root_.map_mul, Matrix.diagonal_mul_diagonal, Units.mul_inv,
    Matrix.diagonal_one, _root_.map_one]

theorem blockInvolutionMatrix_inv_mul :
    σ.blockInvolutionMatrixInv e (n := n) * σ.blockInvolutionMatrix e = 1 := by
  rw [blockInvolutionMatrix, blockInvolutionMatrixInv, ← Matrix.compRingEquiv_apply,
    ← Matrix.compRingEquiv_apply, ← _root_.map_mul, Matrix.diagonal_mul_diagonal, Units.inv_mul,
    Matrix.diagonal_one, _root_.map_one]

omit [Fintype n] in
theorem transpose_blockInvolutionMatrix [FiniteDimensional K D]
    (hσ : finrank K σ.symmetricSubspace = 3) :
    (σ.blockInvolutionMatrix e (n := n))ᵀ = σ.blockInvolutionMatrix e := by
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
      (σ.blockInvolutionMatrix e).map (algebraMap L R) * (matrixChartR e R x)ᵀ *
        (σ.blockInvolutionMatrixInv e).map (algebraMap L R) := by
  rw [matrixChartR_eq_comp, matrixChartR_eq_comp, blockInvolutionMatrix,
    blockInvolutionMatrixInv, ← Matrix.comp_map_map, ← Matrix.comp_map_map,
    Matrix.transpose_comp, ← Matrix.compRingEquiv_apply, ← Matrix.compRingEquiv_apply,
    ← Matrix.compRingEquiv_apply, ← Matrix.compRingEquiv_apply, ← _root_.map_mul,
    ← _root_.map_mul]
  congr 1
  ext i j : 1
  have hd : ∀ d : n → Matrix (Fin 2) (Fin 2) L,
      ((Matrix.diagonal d).map fun M' => M'.map (algebraMap L R)) =
        Matrix.diagonal fun m => (d m).map (algebraMap L R) :=
    fun d => Matrix.diagonal_map (by simp)
  rw [hd, hd, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.map_apply, Matrix.transpose_apply, blockChartR_apply,
    blockChartR_apply, coefficientEquiv_baseChange, chartR_baseChange]

end Involution

end FirstKindInvolution

namespace FirstKindInvolution

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  {L : Type u} [Field L] [Algebra K L]
  (e : L ⊗[K] D ≃ₐ[L] Matrix (Fin 2) (Fin 2) L)
  {n : Type} [Fintype n] [DecidableEq n]

section ReducedNorm

/-- The matrix chart over `L` as an `L`-algebra isomorphism. -/
def matrixChartL : L ⊗[K] Matrix n n D ≃ₐ[L] Matrix (n × Fin 2) (n × Fin 2) L :=
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

/-- A trace-valued antihermitian matrix is `V - ᵗV^σ` for some matrix `V`. -/
theorem IsAntihermitian.exists_eq_sub {H : Matrix n n D} (hH : σ.IsAntihermitian H) :
    ∃ V : Matrix n n D, H = V - σ.matrix n V := by
  choose a ha using fun i => (σ.mem_alternatingSubspace).1 (hH.2 i)
  have hent : ∀ i j, σ (H j i) = -H i j := fun i j => by
    simpa using congrFun (congrFun hH.1 i) j
  let o := Fintype.equivFin n
  refine ⟨Matrix.of fun i j => if o i < o j then H i j else if i = j then a i else 0, ?_⟩
  ext i j
  simp only [Matrix.sub_apply, matrix_apply, Matrix.of_apply]
  rcases lt_trichotomy (o i) (o j) with h | h | h
  · have hne : j ≠ i := fun hji => (lt_irrefl _ (hji ▸ h))
    simp [h, lt_asymm h, hne]
  · have hij : i = j := o.injective h
    subst hij
    simp [ha]
  · have hne : i ≠ j := fun hij => (lt_irrefl _ (hij ▸ h))
    simp [h, lt_asymm h, hne, hent]

/-- The Gram matrix `C = H̃ S̃` over `L` of the split form. -/
def splitGram (H : Matrix n n D) : Matrix (n × Fin 2) (n × Fin 2) L :=
  matrixChartR e L (1 ⊗ₜ[K] H) * σ.blockInvolutionMatrix e

theorem matrixChartL_baseChange (x : L ⊗[K] Matrix n n D) :
    matrixChartR e L ((σ.matrix n).baseChange L x) =
      σ.blockInvolutionMatrix e * (matrixChartR e L x)ᵀ * σ.blockInvolutionMatrixInv e := by
  simpa [Algebra.algebraMap_self] using matrixChartR_baseChange e σ L x

/-- For antihermitian `H`, when the symmetric elements of `σ` have dimension `3`, the split Gram
matrix is `W - Wᵀ`. -/
theorem exists_splitGram_eq_sub [FiniteDimensional K D] (hσ : finrank K σ.symmetricSubspace = 3)
    {H : Matrix n n D} (hH : σ.IsAntihermitian H) :
    ∃ W : Matrix (n × Fin 2) (n × Fin 2) L, σ.splitGram e H = W - Wᵀ := by
  obtain ⟨V, rfl⟩ := IsAntihermitian.exists_eq_sub σ hH
  refine ⟨matrixChartR e L (1 ⊗ₜ[K] V) * σ.blockInvolutionMatrix e, ?_⟩
  have h := matrixChartL_baseChange e σ (1 ⊗ₜ[K] V)
  rw [baseChange_tmul] at h
  rw [splitGram, TensorProduct.tmul_sub, _root_.map_sub, h, Matrix.sub_mul, Matrix.transpose_mul,
    transpose_blockInvolutionMatrix e σ hσ, Matrix.mul_assoc, blockInvolutionMatrix_inv_mul,
    Matrix.mul_one]

theorem transpose_splitGram [FiniteDimensional K D] (hσ : finrank K σ.symmetricSubspace = 3)
    {H : Matrix n n D} (hH : σ.IsAntihermitian H) :
    (σ.splitGram e H)ᵀ = -σ.splitGram e H := by
  obtain ⟨W, hW⟩ := exists_splitGram_eq_sub e σ hσ hH
  rw [hW, Matrix.transpose_sub, Matrix.transpose_transpose, neg_sub]

theorem splitGram_diag [FiniteDimensional K D] (hσ : finrank K σ.symmetricSubspace = 3)
    {H : Matrix n n D} (hH : σ.IsAntihermitian H) (p : n × Fin 2) :
    σ.splitGram e H p p = 0 := by
  obtain ⟨W, hW⟩ := exists_splitGram_eq_sub e σ hσ hH
  rw [hW, Matrix.sub_apply, Matrix.transpose_apply, sub_self]

theorem det_splitGram_ne_zero {H : Matrix n n D} (hu : IsUnit H) :
    (σ.splitGram e H).det ≠ 0 := by
  have h1 : IsUnit (matrixChartR e L (1 ⊗ₜ[K] H)) :=
    (hu.map (Algebra.TensorProduct.includeRight : Matrix n n D →ₐ[K] L ⊗[K] _)).map
      (matrixChartR e L)
  have h2 : IsUnit (σ.blockInvolutionMatrix e (n := n)) :=
    ⟨⟨_, _, blockInvolutionMatrix_mul_inv e σ, blockInvolutionMatrix_inv_mul e σ⟩, rfl⟩
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (h1.mul h2)).ne_zero

/-- The unitary condition `u H ᵗu^σ = H` becomes `g C gᵀ = C` for `g` the matrix chart of `u`
and `C` the split Gram matrix. -/
theorem mul_mul_baseChange_eq_iff (R : Type u) [CommRing R] [Algebra K R] [Algebra L R]
    [IsScalarTower K L R] (H : Matrix n n D) (u : R ⊗[K] Matrix n n D) :
    u * (1 ⊗ₜ[K] H) * (σ.matrix n).baseChange R u = 1 ⊗ₜ[K] H ↔
      matrixChartR e R u * (σ.splitGram e H).map (algebraMap L R) * (matrixChartR e R u)ᵀ =
        (σ.splitGram e H).map (algebraMap L R) := by
  set S := (σ.blockInvolutionMatrix e (n := n)).map (algebraMap L R)
  set S' := (σ.blockInvolutionMatrixInv e (n := n)).map (algebraMap L R)
  have hSS' : S * S' = 1 := by
    rw [← Matrix.map_mul, blockInvolutionMatrix_mul_inv, Matrix.map_one _ (_root_.map_zero _)
      (_root_.map_one _)]
  have hS'S : S' * S = 1 := by
    rw [← Matrix.map_mul, blockInvolutionMatrix_inv_mul, Matrix.map_one _ (_root_.map_zero _)
      (_root_.map_one _)]
  set g := matrixChartR e R u
  set Ht := matrixChartR e R (1 ⊗ₜ[K] H)
  have hC : (σ.splitGram e H).map (algebraMap L R) = Ht * S := by
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

end FirstKindInvolution

end Langlands.GroupScheme.Quaternionic
