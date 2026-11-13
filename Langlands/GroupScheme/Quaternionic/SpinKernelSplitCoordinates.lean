import Langlands.GroupScheme.OrthogonalMatrix.AdaptedHyperbolic
import Langlands.GroupScheme.OrthogonalMatrix.Comparison
import Langlands.GroupScheme.OrthogonalMatrix.Torus
import Langlands.GroupScheme.Quaternionic.QuaternionicMoritaIsometryProof
import Langlands.GroupScheme.Quaternionic.LeviGroupScheme

/-! # Split orthogonal coordinates adapted to the quaternionic Levi torus

Let `D` be a finite-dimensional division algebra over `K` with an involution of the first
kind `σ` whose symmetric subspace has dimension `3`, let `q` be a nondegenerate
`σ`-quadratic form on `D^m` with a hyperbolic pair `h`, and let
`e : L ⊗[K] D ≃ₐ[L] M₂(L)` be a matrix chart over an algebraically closed field `L`.

`exists_adaptedCoordinates` identifies the base change of `O(q)` to `L` with the split
orthogonal group `OrthogonalMatrix.groupScheme (Fin m) L` so that the extended Levi matrix
of every unit with chart `diag(s, 1)` becomes `diag(s, 1, …, 1, s⁻¹, 1, …, 1)`.
The chart of the extended Levi matrix is `1 + (s - 1) α₁ β₁ + (s⁻¹ - 1) α₂ β₂`
(`chartN_extendUnits_hyperbolicLevi`) for explicit vectors with `βᵢ ⬝ αⱼ = δᵢⱼ`; the
coordinates come from `OrthogonalMatrix.exists_weight_adapted_matrix`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic.SplitCoordinates

open FirstKindInvolution MoritaIsometry

section Vectors

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  {L : Type u} [Field L] [Algebra K L]
  (e : L ⊗[K] D ≃ₐ[L] Matrix (Fin 2) (Fin 2) L) (σ : FirstKindInvolution K D)
  {m : ℕ} (q : σ.QuadraticForms (Fin m)) (v w : Fin m → D)

/-- The chart on constants, `d ↦ e (1 ⊗ d)`. -/
def constChart : D →ₐ[K] Matrix (Fin 2) (Fin 2) L :=
  (e.toAlgHom.restrictScalars K).comp Algebra.TensorProduct.includeRight

theorem constChart_apply (d : D) : constChart e d = e (1 ⊗ₜ[K] d) := rfl

/-- A vector indexed by `Fin m × Fin 2`, read in the indices `Fin (2 * m)`. -/
def blockVec {A : Type*} (x : Fin m × Fin 2 → A) : Fin (2 * m) → A :=
  fun p => x ((blockIndex m).symm p)

/-- The first column vector: column `0` of the charts of the first retraction column. -/
def col₁ : Fin m × Fin 2 → L :=
  fun p => constChart e (planeRetraction σ q v w p.1 0) p.2 0

/-- The first row vector: row `0` of the charts of the first plane vector. -/
def row₁ : Fin m × Fin 2 → L :=
  fun p => constChart e (planeInclusion v w 0 p.1) 0 p.2

/-- The second column vector, twisted by the involution matrix `S`. -/
def col₂ : Fin m × Fin 2 → L :=
  fun p => (constChart e (planeRetraction σ q v w p.1 1) *
    (σ.involutionMatrix e : Matrix (Fin 2) (Fin 2) L)) p.2 0

/-- The second row vector, twisted by `S⁻¹`. -/
def row₂ : Fin m × Fin 2 → L :=
  fun p => (((σ.involutionMatrix e)⁻¹ : (Matrix (Fin 2) (Fin 2) L)ˣ) *
    constChart e (planeInclusion v w 1 p.1)) 0 p.2

omit [DivisionRing D] [Algebra K D] [Algebra K L] in
theorem blockVec_dotProduct (x y : Fin m × Fin 2 → L) :
    blockVec x ⬝ᵥ blockVec y = ∑ i : Fin m, ∑ a : Fin 2, x (i, a) * y (i, a) := by
  rw [dotProduct]
  rw [← Fintype.sum_prod_type']
  exact Equiv.sum_comp (blockIndex m).symm (fun p => x p * y p)

omit [DivisionRing D] [Algebra K D] [Algebra K L] in
theorem block_sum (A : Matrix (Fin 2) (Fin m) (Matrix (Fin 2) (Fin 2) L))
    (B : Matrix (Fin m) (Fin 2) (Matrix (Fin 2) (Fin 2) L)) (X Y : Matrix (Fin 2) (Fin 2) L)
    (k k' a b : Fin 2) :
    ∑ j : Fin m, ∑ c : Fin 2, (X * A k j) a c * (B j k' * Y) c b = (X * (A * B) k k' * Y) a b := by
  rw [Matrix.mul_apply (M := A) (N := B), Finset.mul_sum, Finset.sum_mul, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show X * (A k j * B j k') * Y = (X * A k j) * (B j k' * Y) by
    simp only [Matrix.mul_assoc], Matrix.mul_apply]

variable {σ q v w}

include e in
theorem planeChart_mul (h : σ.IsHyperbolicPair q v w) :
    (planeInclusion v w).map (constChart e) * (planeRetraction σ q v w).map (constChart e) = 1 := by
  have h1 := congrArg (fun M => M.map (constChart e).toRingHom) h.planeInclusion_mul_retraction
  simp only [Matrix.map_mul] at h1
  rw [Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)] at h1
  exact h1

theorem row₁_col₁ (h : σ.IsHyperbolicPair q v w) :
    blockVec (row₁ e v w) ⬝ᵥ blockVec (col₁ e σ q v w) = 1 := by
  rw [blockVec_dotProduct]
  have := block_sum ((planeInclusion v w).map (constChart e))
    ((planeRetraction σ q v w).map (constChart e)) 1 1 0 0 0 0
  rw [planeChart_mul e h] at this
  simpa [row₁, col₁] using this

theorem row₁_col₂ (h : σ.IsHyperbolicPair q v w) :
    blockVec (row₁ e v w) ⬝ᵥ blockVec (col₂ e σ q v w) = 0 := by
  rw [blockVec_dotProduct]
  have := block_sum ((planeInclusion v w).map (constChart e))
    ((planeRetraction σ q v w).map (constChart e)) 1 (σ.involutionMatrix e : Matrix (Fin 2) (Fin 2) L) 0 1 0 0
  rw [planeChart_mul e h] at this
  simpa [row₁, col₂] using this

theorem row₂_col₁ (h : σ.IsHyperbolicPair q v w) :
    blockVec (row₂ e σ v w) ⬝ᵥ blockVec (col₁ e σ q v w) = 0 := by
  rw [blockVec_dotProduct]
  have := block_sum ((planeInclusion v w).map (constChart e))
    ((planeRetraction σ q v w).map (constChart e)) (((σ.involutionMatrix e)⁻¹ : (Matrix (Fin 2) (Fin 2) L)ˣ) :
      Matrix (Fin 2) (Fin 2) L) 1 1 0 0 0
  rw [planeChart_mul e h] at this
  simpa [row₂, col₁] using this

theorem row₂_col₂ (h : σ.IsHyperbolicPair q v w) :
    blockVec (row₂ e σ v w) ⬝ᵥ blockVec (col₂ e σ q v w) = 1 := by
  rw [blockVec_dotProduct]
  have := block_sum ((planeInclusion v w).map (constChart e))
    ((planeRetraction σ q v w).map (constChart e)) (((σ.involutionMatrix e)⁻¹ : (Matrix (Fin 2) (Fin 2) L)ˣ) :
      Matrix (Fin 2) (Fin 2) L) (σ.involutionMatrix e : Matrix (Fin 2) (Fin 2) L) 1 1 0 0
  rw [planeChart_mul e h] at this
  simpa [row₂, col₂, Units.inv_mul] using this

end Vectors

section Chart

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  {L : Type u} [Field L] [Algebra K L]
  (e : L ⊗[K] D ≃ₐ[L] Matrix (Fin 2) (Fin 2) L) (σ : FirstKindInvolution K D)
  {m : ℕ} {q : σ.QuadraticForms (Fin m)} {v w : Fin m → D} (h : σ.IsHyperbolicPair q v w)
  (R : Type u) [CommRing R] [Algebra K R] [Algebra L R] [IsScalarTower K L R]

omit [FiniteDimensional K D] in
theorem coefficientEquiv_eq_equiv (x : R ⊗[K] Matrix (Fin m) (Fin m) D) :
    FiniteAlgebraUnits.MatrixPoints.coefficientEquiv K D R x =
      TensorMatrix.equiv R (Fin m) x := by
  induction x using TensorProduct.inductionOn with
  | tmul r M =>
    ext i j
    rw [FiniteAlgebraUnits.MatrixPoints.coefficientEquiv_tmul, TensorMatrix.equiv_tmul]
  | add x y hx hy => rw [_root_.map_add, _root_.map_add, hx, hy]

omit [FiniteDimensional K D] in
/-- The chart of a matrix over `R ⊗ D` is the block matrix of the charts of its entries. -/
theorem chartN_equiv_symm_apply (M : Matrix (Fin m) (Fin m) (R ⊗[K] D)) (i j : Fin m)
    (a b : Fin 2) :
    chartN e m R ((TensorMatrix.equiv R (Fin m)).symm M) (blockIndex m (i, a))
        (blockIndex m (j, b)) = chartR e R (M i j) a b := by
  rw [chartN_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, matrixChartR_apply, coefficientEquiv_eq_equiv,
    AlgEquiv.apply_symm_apply]

omit [FiniteDimensional K D] in
theorem chartR_one_tmul (d : D) :
    chartR e R ((1 : R) ⊗ₜ[K] d) = (constChart e d).map (algebraMap L R) := by
  rw [chartR_tmul, one_smul, constChart_apply]

omit [FiniteDimensional K D] in
/-- Entries of the extended Levi matrix. -/
theorem extendUnits_hyperbolicLevi_apply (b : (R ⊗[K] D)ˣ) (i j : Fin m) :
    (HyperbolicScheme.extendUnits h R (BinaryAction.hyperbolicLevi (σ.baseChange R) b) :
        Matrix (Fin m) (Fin m) (R ⊗[K] D)) i j =
      (1 : Matrix (Fin m) (Fin m) (R ⊗[K] D)) i j +
        (1 : R) ⊗ₜ[K] planeRetraction σ q v w i 0 * ((b : R ⊗[K] D) - 1) *
          (1 : R) ⊗ₜ[K] planeInclusion v w 0 j +
        (1 : R) ⊗ₜ[K] planeRetraction σ q v w i 1 *
          (σ.baseChange R ((b⁻¹ : (R ⊗[K] D)ˣ) : R ⊗[K] D) - 1) *
          (1 : R) ⊗ₜ[K] planeInclusion v w 1 j := by
  change SplitMatrixExtension.value (HyperbolicScheme.inclusion (K := K) (Fin m) v w R)
    (HyperbolicScheme.retraction (Fin m) σ q v w R)
    (BinaryAction.hyperbolicLevi (σ.baseChange R) b : Matrix (Fin 2) (Fin 2) (R ⊗[K] D)) i j = _
  simp only [SplitMatrixExtension.value, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
    Fin.sum_univ_two, BinaryAction.hyperbolicLevi, MonoidHom.coe_mk, OneHom.coe_mk,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one,
    HyperbolicScheme.inclusion, HyperbolicScheme.retraction, HyperbolicScheme.scalarMatrix,
    Matrix.map_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply, mul_zero, add_zero, zero_add,
    mul_sub, sub_mul, mul_one]
  abel

omit [FiniteDimensional K D] in
theorem chartR_inv_of_eq (b : (R ⊗[K] D)ˣ) (s : Rˣ)
    (hb : chartR e R (b : R ⊗[K] D) = !![(s : R), 0; 0, 1]) :
    chartR e R ((b⁻¹ : (R ⊗[K] D)ˣ) : R ⊗[K] D) = !![((s⁻¹ : Rˣ) : R), 0; 0, 1] := by
  have h1 : chartR e R ((b⁻¹ : (R ⊗[K] D)ˣ) : R ⊗[K] D) * chartR e R (b : R ⊗[K] D) = 1 := by
    rw [← _root_.map_mul, Units.inv_mul, _root_.map_one]
  have h2 : !![(s : R), 0; 0, 1] * !![((s⁻¹ : Rˣ) : R), 0; 0, 1] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hb] at h1
  calc chartR e R ((b⁻¹ : (R ⊗[K] D)ˣ) : R ⊗[K] D)
      = chartR e R ((b⁻¹ : (R ⊗[K] D)ˣ) : R ⊗[K] D) *
          (!![(s : R), 0; 0, 1] * !![((s⁻¹ : Rˣ) : R), 0; 0, 1]) := by rw [h2, Matrix.mul_one]
    _ = !![((s⁻¹ : Rˣ) : R), 0; 0, 1] := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem mul_single_mul_apply (X Y : Matrix (Fin 2) (Fin 2) R) (t : R) (a c : Fin 2) :
    (X * (Matrix.single 0 0 t : Matrix (Fin 2) (Fin 2) R) * Y) a c = X a 0 * t * Y 0 c := by
  simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_two]

omit [FiniteDimensional K D] in
/-- **The extended Levi torus in split coordinates.** If the chart of `b` is `diag(s, 1)`, the
chart of the extended Levi matrix of `b` is `1 + (s - 1) α₁ β₁ + (s⁻¹ - 1) α₂ β₂`. -/
theorem chartN_extendUnits_hyperbolicLevi (b : (R ⊗[K] D)ˣ) (s : Rˣ)
    (hb : chartR e R (b : R ⊗[K] D) = !![(s : R), 0; 0, 1]) :
    chartN e m R ((TensorMatrix.equiv R (Fin m)).symm
        (HyperbolicScheme.extendUnits h R (BinaryAction.hyperbolicLevi (σ.baseChange R) b) :
          Matrix (Fin m) (Fin m) (R ⊗[K] D))) =
      OrthogonalMatrix.weightMatrix (algebraMap L R ∘ blockVec (col₁ e σ q v w))
        (algebraMap L R ∘ blockVec (row₁ e v w)) (algebraMap L R ∘ blockVec (col₂ e σ q v w))
        (algebraMap L R ∘ blockVec (row₂ e σ v w)) (s : R) ((s⁻¹ : Rˣ) : R) := by
  set S : Matrix (Fin 2) (Fin 2) L := (σ.involutionMatrix e : Matrix (Fin 2) (Fin 2) L)
    with hSdef
  set S' : Matrix (Fin 2) (Fin 2) L :=
    (((σ.involutionMatrix e)⁻¹ : (Matrix (Fin 2) (Fin 2) L)ˣ) : Matrix (Fin 2) (Fin 2) L)
    with hS'def
  have hSS' : S.map (algebraMap L R) * S'.map (algebraMap L R) = 1 := by
    rw [← Matrix.map_mul, hSdef, hS'def, Units.mul_inv,
      Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)]
  have hb1 : chartR e R ((b : R ⊗[K] D) - 1) = Matrix.single 0 0 ((s : R) - 1) := by
    rw [_root_.map_sub, _root_.map_one, hb]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hb2 : chartR e R (σ.baseChange R ((b⁻¹ : (R ⊗[K] D)ˣ) : R ⊗[K] D) - 1) =
      S.map (algebraMap L R) * Matrix.single 0 0 (((s⁻¹ : Rˣ) : R) - 1) *
        S'.map (algebraMap L R) := by
    rw [_root_.map_sub, _root_.map_one, chartR_baseChange, chartR_inv_of_eq e R b s hb,
      ← hSS']
    have hd : (!![((s⁻¹ : Rˣ) : R), 0; 0, 1])ᵀ =
        Matrix.single 0 0 (((s⁻¹ : Rˣ) : R) - 1) + 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, add_sub_cancel_right]
  ext p p'
  obtain ⟨⟨i, a⟩, rfl⟩ := (blockIndex m).surjective p
  obtain ⟨⟨j, c⟩, rfl⟩ := (blockIndex m).surjective p'
  rw [chartN_equiv_symm_apply, extendUnits_hyperbolicLevi_apply, _root_.map_add, _root_.map_add,
    _root_.map_mul, _root_.map_mul, _root_.map_mul, _root_.map_mul, hb1, hb2,
    chartR_one_tmul, chartR_one_tmul, chartR_one_tmul, chartR_one_tmul]
  have h3 : ((constChart e (planeRetraction σ q v w i 1)).map (algebraMap L R) *
        (S.map (algebraMap L R) * Matrix.single 0 0 (((s⁻¹ : Rˣ) : R) - 1) *
          S'.map (algebraMap L R)) *
        (constChart e (planeInclusion v w 1 j)).map (algebraMap L R)) =
      ((constChart e (planeRetraction σ q v w i 1) * S).map (algebraMap L R)) *
        Matrix.single 0 0 (((s⁻¹ : Rˣ) : R) - 1) *
        ((S' * constChart e (planeInclusion v w 1 j)).map (algebraMap L R)) := by
    rw [Matrix.map_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  rw [h3, Matrix.add_apply, Matrix.add_apply, mul_single_mul_apply, mul_single_mul_apply]
  simp only [OrthogonalMatrix.weightMatrix, Matrix.add_apply, Matrix.smul_apply,
    vecMulVec_apply, Function.comp_apply, blockVec, Equiv.symm_apply_apply, smul_eq_mul,
    Matrix.map_apply, col₁, row₁, col₂, row₂, hSdef, hS'def]
  have h1 : chartR e R ((1 : Matrix (Fin m) (Fin m) (R ⊗[K] D)) i j) a c =
      (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) R) (blockIndex m (i, a)) (blockIndex m (j, c)) := by
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, _root_.map_one]
      by_cases hac : a = c
      · subst hac
        simp
      · have hne : blockIndex m (i, a) ≠ blockIndex m (i, c) := fun h' =>
          hac (congrArg Prod.snd ((blockIndex m).injective h'))
        simp only [hne, ↓reduceIte, Matrix.one_apply_ne hac]
    · have hne : blockIndex m (i, a) ≠ blockIndex m (j, c) := fun h' =>
        hij (congrArg Prod.fst ((blockIndex m).injective h'))
      simp only [hij, hne, ↓reduceIte, _root_.map_zero, Matrix.zero_apply]
  rw [h1]
  ring

end Chart

section Adapted

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  {L : Type u} [Field L] [Algebra K L]
  (e : L ⊗[K] D ≃ₐ[L] Matrix (Fin 2) (Fin 2) L) (σ : FirstKindInvolution K D)
  {m : ℕ} {q : σ.QuadraticForms (Fin m)} {v w : Fin m → D} (h : σ.IsHyperbolicPair q v w)

/-- The diagonal unit `diag(s, 1)`. -/
def diagUnit {R : Type*} [CommRing R] (s : Rˣ) : (Matrix (Fin 2) (Fin 2) R)ˣ where
  val := !![(s : R), 0; 0, 1]
  inv := !![((s⁻¹ : Rˣ) : R), 0; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

omit [FiniteDimensional K D] in
theorem scalarMatrix_hyperbolicMatrix (R : Type u) [CommRing R] [Algebra K R] :
    HyperbolicScheme.scalarMatrix (K := K) R
        (BinaryAction.hyperbolicMatrix : Matrix (Fin 2) (Fin 2) D) =
      BinaryAction.hyperbolicMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [HyperbolicScheme.scalarMatrix, BinaryAction.hyperbolicMatrix,
      Algebra.TensorProduct.one_def]

omit [FiniteDimensional K D] in
/-- The extended Levi matrix of any unit is an isometry unit of the split representative. -/
theorem extendUnits_levi_mem (R : Type u) [CommRing R] [Algebra K R] (b : (R ⊗[K] D)ˣ) :
    Units.map (TensorMatrix.equiv R (Fin m)).symm.toAlgHom.toMonoidHom
        (HyperbolicScheme.extendUnits h R (BinaryAction.hyperbolicLevi (σ.baseChange R) b)) ∈
      σ.isometryUnits (FirstKindInvolution.IsHyperbolicPair.splitRepresentative
        (σ := σ) (q := q) (e := v) (f := w)) R := by
  change IsometryCut.defect (σ.matrix (Fin m)) _ _ ∈
    (σ.matrix (Fin m)).alternatingSubspace.baseChange R
  rw [IsometryCut.alternatingSubspace_baseChange, Submodule.restrictScalars_mem,
    TensorMatrix.mem_alternating_iff, IsometryCut.defect, _root_.map_sub, _root_.map_mul,
    _root_.map_mul, TensorMatrix.adjoint]
  have hy : TensorMatrix.equiv R (Fin m)
      ((Units.map (TensorMatrix.equiv R (Fin m)).symm.toAlgHom.toMonoidHom
        (HyperbolicScheme.extendUnits h R (BinaryAction.hyperbolicLevi (σ.baseChange R) b)) :
          (R ⊗[K] Matrix (Fin m) (Fin m) D)ˣ) : R ⊗[K] Matrix (Fin m) (Fin m) D) =
      (HyperbolicScheme.extendUnits h R (BinaryAction.hyperbolicLevi (σ.baseChange R) b) :
        Matrix (Fin m) (Fin m) (R ⊗[K] D)) :=
    (TensorMatrix.equiv R (Fin m)).apply_symm_apply _
  have hQ : TensorMatrix.equiv R (Fin m) ((1 : R) ⊗ₜ[K]
      FirstKindInvolution.IsHyperbolicPair.splitRepresentative (σ := σ) (q := q) (e := v) (f := w)) =
      HyperbolicScheme.scalarMatrix (K := K) R
        (FirstKindInvolution.IsHyperbolicPair.splitRepresentative
          (σ := σ) (q := q) (e := v) (f := w)) := by
    ext i j
    rfl
  rw [hy, hQ]
  refine HyperbolicScheme.extendUnits_preserves h R _ ?_
  rw [scalarMatrix_hyperbolicMatrix]
  change (LeviScheme.leviMatrix σ R b : Matrix (Fin 2) (Fin 2) (R ⊗[K] D)) *
      BinaryAction.hyperbolicMatrix * (σ.baseChange R).matrix (Fin 2) (LeviScheme.leviMatrix σ R b) -
    BinaryAction.hyperbolicMatrix ∈ _
  rw [LeviScheme.leviMatrix_isometry, sub_self]
  exact Submodule.zero_mem _

variable (hσ : Module.finrank K σ.symmetricSubspace = 3)

include h hσ in
/-- Over `L` itself, the torus element of every unit `s` preserves the split Gram matrix. -/
theorem isAlt_weightMatrix_gramN (s : Lˣ) :
    OrthogonalMatrix.IsAlt
      (OrthogonalMatrix.weightMatrix (blockVec (col₁ e σ q v w)) (blockVec (row₁ e v w))
          (blockVec (col₂ e σ q v w)) (blockVec (row₂ e σ v w)) (s : L) (s : L)⁻¹ *
        gramN e σ m (FirstKindInvolution.IsHyperbolicPair.splitRepresentative
          (σ := σ) (q := q) (e := v) (f := w)) *
        (OrthogonalMatrix.weightMatrix (blockVec (col₁ e σ q v w)) (blockVec (row₁ e v w))
          (blockVec (col₂ e σ q v w)) (blockVec (row₂ e σ v w)) (s : L) (s : L)⁻¹)ᵀ -
        gramN e σ m (FirstKindInvolution.IsHyperbolicPair.splitRepresentative
          (σ := σ) (q := q) (e := v) (f := w))) := by
  set b : (L ⊗[K] D)ˣ := Units.map (chartR e L).symm.toMonoidHom (diagUnit s) with hbdef
  have hb : chartR e L (b : L ⊗[K] D) = !![(s : L), 0; 0, 1] :=
    (chartR e L).apply_symm_apply _
  have hmem := extendUnits_levi_mem σ h L b
  rw [mem_isometryUnits_iff e σ m L hσ] at hmem
  obtain ⟨Y, hY⟩ := hmem
  have hc := chartN_extendUnits_hyperbolicLevi e σ h L b s hb
  have hmap : ∀ M : Matrix (Fin (2 * m)) (Fin (2 * m)) L, M.map (algebraMap L L) = M :=
    fun M => by ext i j; simp
  have hcomp : ∀ x : Fin (2 * m) → L, algebraMap L L ∘ x = x := fun x => by funext i; simp
  set g := HyperbolicScheme.extendUnits h L (BinaryAction.hyperbolicLevi (σ.baseChange L) b)
  set C := gramN e σ m (FirstKindInvolution.IsHyperbolicPair.splitRepresentative
    (σ := σ) (q := q) (e := v) (f := w))
  have hY' : chartN e m L ((TensorMatrix.equiv L (Fin m)).symm
        (g : Matrix (Fin m) (Fin m) (L ⊗[K] D))) * C.map (algebraMap L L) *
      (chartN e m L ((TensorMatrix.equiv L (Fin m)).symm
        (g : Matrix (Fin m) (Fin m) (L ⊗[K] D))))ᵀ - C.map (algebraMap L L) = Y - Yᵀ := hY
  rw [hc, hmap, hcomp, hcomp, hcomp, hcomp, Units.val_inv_eq_inv_val] at hY'
  exact ⟨Y, hY'⟩

end Adapted

section Iso

attribute [local instance] restrictedSectionsAlgebra restrictedSectionsScalarTower

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  {L : Type u} [Field L] [Algebra K L]
  (e : L ⊗[K] D ≃ₐ[L] Matrix (Fin 2) (Fin 2) L) (σ : FirstKindInvolution K D) (m : ℕ)
  (hσ : Module.finrank K σ.symmetricSubspace = 3)
  (q : σ.QuadraticForms (Fin m)) (Q₀ : Matrix (Fin m) (Fin m) D)
  (hQ₀ : (Submodule.Quotient.mk Q₀ : σ.QuadraticForms (Fin m)) = q)
  (P : Matrix (Fin m ⊕ Fin m) (Fin (2 * m)) L) (P' : Matrix (Fin (2 * m)) (Fin m ⊕ Fin m) L)
  (hPP' : P * P' = 1) (hP'P : P' * P = 1)
  (hPQ : OrthogonalMatrix.IsAlt (P * (gramN e σ m Q₀).map (algebraMap L L) * Pᵀ -
    OrthogonalMatrix.formMatrix (Fin m) L))

include hPP' hP'P hPQ

/-- The split model of points read in the orthogonal coordinates `P`: `u ↦ P U P'`. -/
def splitModelHom (U : Over (Spec (CommRingCat.of L))) :
    splitModel e σ m Q₀ U →*
      OrthogonalMatrix.orthogonalGroup (Fin m) ((algΓ (CommRingCat.of L)).obj U).unop where
  toFun z := ⟨OrthogonalMatrix.splitMatrix L P P' ((algΓ (CommRingCat.of L)).obj U).unop
      ((z : (((algΓ (CommRingCat.of L)).obj U).unop ⊗[L]
        Matrix (Fin (2 * m)) (Fin (2 * m)) L)ˣ) :
          ((algΓ (CommRingCat.of L)).obj U).unop ⊗[L] Matrix (Fin (2 * m)) (Fin (2 * m)) L),
    (OrthogonalMatrix.splitMatrix_mem_iff P P' _ hP'P hPQ _).2 z.2⟩
  map_one' := by
    apply Subtype.ext
    change OrthogonalMatrix.splitMatrix L P P' ((algΓ (CommRingCat.of L)).obj U).unop
      (((1 : splitModel e σ m Q₀ U) : (((algΓ (CommRingCat.of L)).obj U).unop ⊗[L]
        Matrix (Fin (2 * m)) (Fin (2 * m)) L)ˣ) :
          ((algΓ (CommRingCat.of L)).obj U).unop ⊗[L] Matrix (Fin (2 * m)) (Fin (2 * m)) L) =
      (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ((algΓ (CommRingCat.of L)).obj U).unop)
    rw [OneMemClass.coe_one, Units.val_one]
    exact OrthogonalMatrix.splitMatrix_one P P' _ hPP'
  map_mul' z z' := by
    apply Subtype.ext
    change OrthogonalMatrix.splitMatrix L P P' ((algΓ (CommRingCat.of L)).obj U).unop
      (((z * z' : splitModel e σ m Q₀ U) : (((algΓ (CommRingCat.of L)).obj U).unop ⊗[L]
        Matrix (Fin (2 * m)) (Fin (2 * m)) L)ˣ) :
          ((algΓ (CommRingCat.of L)).obj U).unop ⊗[L] Matrix (Fin (2 * m)) (Fin (2 * m)) L) =
      OrthogonalMatrix.splitMatrix L P P' ((algΓ (CommRingCat.of L)).obj U).unop
        ((z : (((algΓ (CommRingCat.of L)).obj U).unop ⊗[L]
          Matrix (Fin (2 * m)) (Fin (2 * m)) L)ˣ) :
            ((algΓ (CommRingCat.of L)).obj U).unop ⊗[L] Matrix (Fin (2 * m)) (Fin (2 * m)) L) *
      OrthogonalMatrix.splitMatrix L P P' ((algΓ (CommRingCat.of L)).obj U).unop
        ((z' : (((algΓ (CommRingCat.of L)).obj U).unop ⊗[L]
          Matrix (Fin (2 * m)) (Fin (2 * m)) L)ˣ) :
            ((algΓ (CommRingCat.of L)).obj U).unop ⊗[L] Matrix (Fin (2 * m)) (Fin (2 * m)) L)
    rw [Subgroup.coe_mul, Units.val_mul]
    exact OrthogonalMatrix.splitMatrix_mul P P' _ hP'P _ _

omit [FiniteDimensional K D] in
theorem coe_splitModelHom (U : Over (Spec (CommRingCat.of L))) (z : splitModel e σ m Q₀ U) :
    ((splitModelHom e σ m Q₀ P P' hPP' hP'P hPQ U z :
        OrthogonalMatrix.orthogonalGroup (Fin m) ((algΓ (CommRingCat.of L)).obj U).unop) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ((algΓ (CommRingCat.of L)).obj U).unop) =
      OrthogonalMatrix.splitMatrix L P P' ((algΓ (CommRingCat.of L)).obj U).unop
        ((z : (((algΓ (CommRingCat.of L)).obj U).unop ⊗[L]
          Matrix (Fin (2 * m)) (Fin (2 * m)) L)ˣ) :
            ((algΓ (CommRingCat.of L)).obj U).unop ⊗[L] Matrix (Fin (2 * m)) (Fin (2 * m)) L) :=
  rfl

omit [FiniteDimensional K D] in
theorem splitModelHom_bijective (U : Over (Spec (CommRingCat.of L))) :
    Function.Bijective (splitModelHom e σ m Q₀ P P' hPP' hP'P hPQ U) := by
  constructor
  · intro z z' hzz'
    have h1 := congrArg Subtype.val hzz'
    rw [coe_splitModelHom, coe_splitModelHom] at h1
    exact Subtype.ext (Units.ext (OrthogonalMatrix.splitMatrix_injective P P' _ hP'P h1))
  · intro g
    obtain ⟨w, hw, hwg⟩ := OrthogonalMatrix.exists_splitMatrix_eq P P' _ hPP' hP'P hPQ g
    exact ⟨⟨w, hw⟩, Subtype.ext hwg⟩

/-- Points of the base change of `O(q)` as split orthogonal matrices. -/
def adaptedPointsEquiv (U : Over (Spec (CommRingCat.of L))) :
    (U ⟶ ((GroupScheme.baseChange (scalarBaseMap K L)).obj (σ.isometryGroup q)).X) ≃*
      OrthogonalMatrix.orthogonalGroup (Fin m) Γ(U.left, ⊤) :=
  (basePointsEquiv e σ m hσ q Q₀ hQ₀ U).trans
    (MulEquiv.ofBijective (splitModelHom e σ m Q₀ P P' hPP' hP'P hPQ U)
      (splitModelHom_bijective e σ m Q₀ P P' hPP' hP'P hPQ U))

theorem coe_adaptedPointsEquiv (U : Over (Spec (CommRingCat.of L)))
    (x : U ⟶ ((GroupScheme.baseChange (scalarBaseMap K L)).obj (σ.isometryGroup q)).X) :
    ((adaptedPointsEquiv e σ m hσ q Q₀ hQ₀ P P' hPP' hP'P hPQ U x :
        OrthogonalMatrix.orthogonalGroup (Fin m) Γ(U.left, ⊤)) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) Γ(U.left, ⊤)) =
      OrthogonalMatrix.splitMatrix L P P' ((algΓ (CommRingCat.of L)).obj U).unop
        ((basePointsEquiv e σ m hσ q Q₀ hQ₀ U x : (((algΓ (CommRingCat.of L)).obj U).unop ⊗[L]
          Matrix (Fin (2 * m)) (Fin (2 * m)) L)ˣ) :
            ((algΓ (CommRingCat.of L)).obj U).unop ⊗[L] Matrix (Fin (2 * m)) (Fin (2 * m)) L) :=
  rfl

theorem adaptedPointsEquiv_naturality {U U' : Over (Spec (CommRingCat.of L))} (a : U' ⟶ U)
    (x : U ⟶ ((GroupScheme.baseChange (scalarBaseMap K L)).obj (σ.isometryGroup q)).X) :
    adaptedPointsEquiv e σ m hσ q Q₀ hQ₀ P P' hPP' hP'P hPQ U' (a ≫ x) =
      OrthogonalMatrix.map (Fin m) a.left.appTop.hom
        (adaptedPointsEquiv e σ m hσ q Q₀ hQ₀ P P' hPP' hP'P hPQ U x) := by
  apply Subtype.ext
  rw [coe_adaptedPointsEquiv, OrthogonalMatrix.coe_map, coe_adaptedPointsEquiv,
    basePointsEquiv_naturality, IsometryCut.coe_isometrySubgroupMap]
  exact OrthogonalMatrix.splitMatrix_naturality (K := L) P P' _
    ((algΓ (CommRingCat.of L)).map a).unop.hom _

/-- **Adapted splitting of `O(q)`.** The base change of `O(q)` to `L` is the split orthogonal
group, on points by `u ↦ P U P'`. -/
def adaptedIso :
    (GroupScheme.baseChange (scalarBaseMap K L)).obj (σ.isometryGroup q) ≅
      OrthogonalMatrix.groupScheme (Fin m) (CommRingCat.of L) :=
  isoOfPointModels (fun U => OrthogonalMatrix.orthogonalGroup (Fin m) Γ(U.left, ⊤))
    (fun a => OrthogonalMatrix.map (Fin m) a.left.appTop.hom)
    (adaptedPointsEquiv e σ m hσ q Q₀ hQ₀ P P' hPP' hP'P hPQ)
    (OrthogonalMatrix.pointsEquiv (Fin m) (CommRingCat.of L))
    (adaptedPointsEquiv_naturality e σ m hσ q Q₀ hQ₀ P P' hPP' hP'P hPQ)
    (fun a y => OrthogonalMatrix.pointsEquiv_naturality a y)

theorem pointsEquiv_adaptedIso (U : Over (Spec (CommRingCat.of L)))
    (x : U ⟶ ((GroupScheme.baseChange (scalarBaseMap K L)).obj (σ.isometryGroup q)).X) :
    OrthogonalMatrix.pointsEquiv (Fin m) (CommRingCat.of L) U
        (x ≫ (adaptedIso e σ m hσ q Q₀ hQ₀ P P' hPP' hP'P hPQ).hom.hom.hom) =
      adaptedPointsEquiv e σ m hσ q Q₀ hQ₀ P P' hPP' hP'P hPQ U x :=
  isoOfPointModels_hom (fun U => OrthogonalMatrix.orthogonalGroup (Fin m) Γ(U.left, ⊤))
    (fun a => OrthogonalMatrix.map (Fin m) a.left.appTop.hom)
    (adaptedPointsEquiv e σ m hσ q Q₀ hQ₀ P P' hPP' hP'P hPQ)
    (OrthogonalMatrix.pointsEquiv (Fin m) (CommRingCat.of L))
    (adaptedPointsEquiv_naturality e σ m hσ q Q₀ hQ₀ P P' hPP' hP'P hPQ)
    (fun a y => OrthogonalMatrix.pointsEquiv_naturality a y) U x

end Iso

section Main

/-- The diagonal Levi matrix of `(s, 1, …, 1)` is `1 + (s - 1) E₀₀ + (s⁻¹ - 1) E₀'₀'`. -/
theorem one_add_single_eq_levi {A : Type*} [CommRing A] {k : ℕ} (s : Aˣ) :
    (1 + Matrix.single (Sum.inl 0) (Sum.inl 0) ((s : A) - 1) +
        Matrix.single (Sum.inr 0) (Sum.inr 0) (((s⁻¹ : Aˣ) : A) - 1) :
          Matrix (Fin (k + 1) ⊕ Fin (k + 1)) (Fin (k + 1) ⊕ Fin (k + 1)) A) =
      SymplecticMatrix.levi (GeneralLinear.diagonalTorusUnits (Fin (k + 1)) A
        (Pi.mulSingle (ULift.up.{u} (0 : Fin (k + 1))) s)) := by
  rw [SymplecticMatrix.levi_diagonalTorusUnits]
  ext (i | i) (j | j) <;> by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
    by_cases hij : i = j <;>
    simp_all [Matrix.add_apply, Matrix.single_apply, SymplecticMatrix.torusWeights,
      Pi.mulSingle_apply]
  all_goals
    intro h0
    subst h0
    simp_all

attribute [local instance] restrictedSectionsAlgebra restrictedSectionsScalarTower

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  {L : Type u} [Field L] [Algebra K L]
  (e : L ⊗[K] D ≃ₐ[L] Matrix (Fin 2) (Fin 2) L) (σ : FirstKindInvolution K D)
  (hσ : Module.finrank K σ.symmetricSubspace = 3)

theorem map_conj_single {A : Type*} [CommRing A] (f : L →+* A) {n : Type} [Fintype n]
    {k : ℕ} {P : Matrix (Fin k ⊕ Fin k) n L} {P' : Matrix n (Fin k ⊕ Fin k) L} {α β : n → L}
    {i : Fin k ⊕ Fin k} (h : P * vecMulVec α β * P' = Matrix.single i i 1) :
    P.map f * vecMulVec (f ∘ α) (f ∘ β) * P'.map f = Matrix.single i i 1 := by
  have h1 := congrArg (fun M => M.map f) h
  simp only [Matrix.map_mul] at h1
  have h2 : (vecMulVec α β).map f = vecMulVec (f ∘ α) (f ∘ β) := by
    ext a b
    simp [vecMulVec_apply]
  rw [h2] at h1
  rw [h1]
  ext a b
  simp [Matrix.single_apply]

set_option maxHeartbeats 800000 in
include hσ in
/-- **Adapted split orthogonal coordinates.** Over an algebraically closed field `L` with a
matrix chart `e` of `L ⊗ D`, the base change of `O(q)` is isomorphic to the split orthogonal
group by an isomorphism `Φ` under which the extended Levi matrix of every unit `b` with chart
`diag(s, 1)` becomes the diagonal torus element `diag(s, 1, …, 1, s⁻¹, 1, …, 1)`. -/
theorem exists_adaptedCoordinates [IsAlgClosed L] {m : ℕ} (hm : 0 < m)
    {q : σ.QuadraticForms (Fin m)} (hq : σ.IsNondegenerateQuadratic q) {v w : Fin m → D}
    (h : σ.IsHyperbolicPair q v w) :
    ∃ Φ : (GroupScheme.baseChange (scalarBaseMap K L)).obj (σ.isometryGroup q) ≅
        OrthogonalMatrix.groupScheme (Fin m) (CommRingCat.of L),
      ∀ (U : Over (Spec (CommRingCat.of L)))
        (x : U ⟶ ((GroupScheme.baseChange (scalarBaseMap K L)).obj (σ.isometryGroup q)).X)
        (b : (restrictedSections K L U ⊗[K] D)ˣ) (s : (restrictedSections K L U)ˣ),
        chartR e (restrictedSections K L U) (b : restrictedSections K L U ⊗[K] D) =
          !![(s : restrictedSections K L U), 0; 0, 1] →
        HyperbolicScheme.matrixPointsEquiv (Fin m) ((Over.map (scalarBaseMap K L)).obj U)
            (GroupScheme.baseChangePointsEquiv (scalarBaseMap K L) (σ.isometryGroup q) U x ≫
              (σ.isometryGroupι q).hom.hom) =
          HyperbolicScheme.extendUnits h (restrictedSections K L U)
            (BinaryAction.hyperbolicLevi (σ.baseChange (restrictedSections K L U)) b) →
        (OrthogonalMatrix.pointsEquiv (Fin m) (CommRingCat.of L) U (x ≫ Φ.hom.hom.hom) :
            Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) Γ(U.left, ⊤)) =
          (OrthogonalMatrix.leviHom Γ(U.left, ⊤)
            (GeneralLinear.diagonalTorusUnits (Fin m) Γ(U.left, ⊤)
              (Pi.mulSingle (ULift.up.{u} (⟨0, hm⟩ : Fin m)) s)) :
            Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) Γ(U.left, ⊤)) := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  set Q₀ := FirstKindInvolution.IsHyperbolicPair.splitRepresentative
    (σ := σ) (q := q) (e := v) (f := w) with hQ₀def
  have hQ₀ : (Submodule.Quotient.mk Q₀ : σ.QuadraticForms (Fin (k + 1))) = q :=
    h.mk_splitRepresentative
  set C := gramN e σ (k + 1) Q₀ with hCdef
  have hC : IsUnit (C + Cᵀ) := isNondegenerateQuadratic_gramN e σ (k + 1) hσ q Q₀ hQ₀ hq
  -- a torus parameter `s₀` with `s₀² ≠ 1`
  obtain ⟨x₀, hx₀⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset L)
  have hx0 : x₀ ≠ 0 := fun h0 => hx₀ (by simp [h0])
  have hx2 : x₀ ^ 2 ≠ 1 := by
    intro h2
    have : (x₀ - 1) * (x₀ + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 this with h3 | h3
    · exact hx₀ (by simp [sub_eq_zero.1 h3])
    · exact hx₀ (by simp [eq_neg_of_add_eq_zero_left h3])
  obtain ⟨P, P', hPP', hP'P, hPalt, h₁, h₂⟩ :=
    OrthogonalMatrix.exists_weight_adapted_matrix (k := k)
      (by rw [Fintype.card_fin]) C hC (row₁_col₁ e h) (row₁_col₂ e h) (row₂_col₁ e h)
      (row₂_col₂ e h) hx0 hx2
      (isAlt_weightMatrix_gramN e σ h hσ (Units.mk0 x₀ hx0))
  have hmap : C.map (algebraMap L L) = C := by
    ext i j
    simp
  have hPQ : OrthogonalMatrix.IsAlt (P * C.map (algebraMap L L) * Pᵀ -
      OrthogonalMatrix.formMatrix (Fin (k + 1)) L) := by
    rw [hmap]
    exact hPalt
  refine ⟨adaptedIso e σ (k + 1) hσ q Q₀ hQ₀ P P' hPP' hP'P hPQ, ?_⟩
  intro U x b s hb hx
  rw [pointsEquiv_adaptedIso, coe_adaptedPointsEquiv]
  have hyx : TensorMatrix.equiv (restrictedSections K L U) (Fin (k + 1))
      (((σ.isometryPointsEquiv q Q₀ hQ₀ ((Over.map (scalarBaseMap K L)).obj U)
        (GroupScheme.baseChangePointsEquiv (scalarBaseMap K L) (σ.isometryGroup q) U x) :
          (restrictedSections K L U ⊗[K] Matrix (Fin (k + 1)) (Fin (k + 1)) D)ˣ)) :
        restrictedSections K L U ⊗[K] Matrix (Fin (k + 1)) (Fin (k + 1)) D) =
      (HyperbolicScheme.extendUnits h (restrictedSections K L U)
        (BinaryAction.hyperbolicLevi (σ.baseChange (restrictedSections K L U)) b) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) (restrictedSections K L U ⊗[K] D)) :=
    congrArg Units.val hx
  have hchart := chartN_extendUnits_hyperbolicLevi e σ h (restrictedSections K L U) b s hb
  rw [← hyx, AlgEquiv.symm_apply_apply] at hchart
  have key : OrthogonalMatrix.splitMatrix L P P' (restrictedSections K L U)
      (theta e (k + 1) (restrictedSections K L U)
        (((σ.isometryPointsEquiv q Q₀ hQ₀ ((Over.map (scalarBaseMap K L)).obj U)
          (GroupScheme.baseChangePointsEquiv (scalarBaseMap K L) (σ.isometryGroup q) U x) :
            (restrictedSections K L U ⊗[K] Matrix (Fin (k + 1)) (Fin (k + 1)) D)ˣ)) :
          restrictedSections K L U ⊗[K] Matrix (Fin (k + 1)) (Fin (k + 1)) D)) =
      1 + Matrix.single (Sum.inl 0) (Sum.inl 0) ((s : restrictedSections K L U) - 1) +
        Matrix.single (Sum.inr 0) (Sum.inr 0)
          (((s⁻¹ : (restrictedSections K L U)ˣ) : restrictedSections K L U) - 1) := by
    rw [OrthogonalMatrix.splitMatrix]
    change (P.map (algebraMap L (restrictedSections K L U))) *
      scalarChart L (2 * (k + 1)) (restrictedSections K L U)
        (theta e (k + 1) (restrictedSections K L U) _) *
      P'.map (algebraMap L (restrictedSections K L U)) = _
    rw [scalarChart_theta, hchart]
    exact OrthogonalMatrix.conj_weightMatrix
      (OrthogonalMatrix.map_mul_map_eq_one (restrictedSections K L U) hPP')
      (map_conj_single (algebraMap L (restrictedSections K L U)) h₁)
      (map_conj_single (algebraMap L (restrictedSections K L U)) h₂) _ _
  exact key.trans (one_add_single_eq_levi (k := k) s)

end Main

end Langlands.GroupScheme.Quaternionic.SplitCoordinates
