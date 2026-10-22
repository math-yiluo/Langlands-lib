import Langlands.Global.ArchimedeanCompact
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Data.Matrix.Block

noncomputable section

universe u

open scoped Classical Matrix.Norms.Operator

namespace Langlands.Global

open NumberField NumberField.InfinitePlace

variable (K : Type u) [Field K]

/-- The actual real and complex infinite places, kept as separate summands. -/
abbrev ArchimedeanPlaceIndex :=
  {v : InfinitePlace K // IsReal v} ⊕ {v : InfinitePlace K // IsComplex v}

/-- Evaluation at a place, followed by the usual inclusion of the reals when needed. -/
def archimedeanPlaceEmbedding (v : ArchimedeanPlaceIndex K) :
    mixedEmbedding.mixedSpace K →ₐ[ℝ] ℂ where
  toFun x := Sum.elim (fun v => (x.1 v : ℂ)) (fun v => x.2 v) v
  map_zero' := by cases v <;> simp
  map_one' := by cases v <;> simp
  map_add' x y := by cases v <;> simp
  map_mul' x y := by cases v <;> simp
  commutes' r := by cases v <;> rfl

variable [NumberField K] (n : ℕ)

/-- Coordinates for the direct sum of the local standard complex representations. -/
abbrev ArchimedeanComplexIndex := Fin n × ArchimedeanPlaceIndex K

/-- All local standard matrices, with real entries included in the complex numbers. -/
def archimedeanLocalMatrices : ArchimedeanMatrix K n →ₐ[ℝ]
    (ArchimedeanPlaceIndex K → Matrix (Fin n) (Fin n) ℂ) :=
  AlgHom.pi (fun v => (archimedeanPlaceEmbedding K v).mapMatrix)

/-- The concrete block diagonal matrix of all infinite-place matrices. -/
def archimedeanComplexification : ArchimedeanMatrix K n →ₐ[ℝ]
    Matrix (ArchimedeanComplexIndex K n) (ArchimedeanComplexIndex K n) ℂ where
  __ := (Matrix.blockDiagonalRingHom (Fin n) (ArchimedeanPlaceIndex K) ℂ).comp
    (archimedeanLocalMatrices K n).toRingHom
  commutes' r := by
    ext ⟨i, v⟩ ⟨j, w⟩
    simp only [AlgHom.toRingHom_eq_coe]
    simp [Matrix.blockDiagonal_apply, Matrix.algebraMap_matrix_apply]
    split_ifs <;> simp_all

@[simp]
theorem archimedeanComplexification_apply (A : ArchimedeanMatrix K n)
    (i j : Fin n) (v w : ArchimedeanPlaceIndex K) :
    archimedeanComplexification K n A (i, v) (j, w) =
      if v = w then archimedeanPlaceEmbedding K v (A i j) else 0 := rfl

@[simp]
theorem archimedeanComplexification_real (A : ArchimedeanMatrix K n)
    (i j : Fin n) (v : {v : InfinitePlace K // IsReal v}) :
    archimedeanComplexification K n A (i, .inl v) (j, .inl v) = ((A i j).1 v : ℂ) := by
  simp [archimedeanPlaceEmbedding]

@[simp]
theorem archimedeanComplexification_complex (A : ArchimedeanMatrix K n)
    (i j : Fin n) (v : {v : InfinitePlace K // IsComplex v}) :
    archimedeanComplexification K n A (i, .inr v) (j, .inr v) = (A i j).2 v := by
  simp [archimedeanPlaceEmbedding]

theorem archimedeanComplexification_injective :
    Function.Injective (archimedeanComplexification K n) := by
  intro A B h
  apply Matrix.ext
  intro i j
  apply Prod.ext
  · funext v
    simpa [archimedeanPlaceEmbedding] using
      congrArg (fun M => M (i, Sum.inl v) (j, Sum.inl v)) h
  · funext v
    simpa [archimedeanPlaceEmbedding] using
      congrArg (fun M => M (i, Sum.inr v) (j, Sum.inr v)) h

theorem isClosedEmbedding_archimedeanComplexification :
    Topology.IsClosedEmbedding (archimedeanComplexification K n) :=
  LinearMap.isClosedEmbedding_of_injective
    (f := (archimedeanComplexification K n).toLinearMap)
    (LinearMap.ker_eq_bot.mpr (archimedeanComplexification_injective K n))

/-- The faithful complex matrix representation of the mixed archimedean group. -/
def archimedeanComplexGL : ArchimedeanGL K n →*
    Matrix.GeneralLinearGroup (ArchimedeanComplexIndex K n) ℂ :=
  Units.map (archimedeanComplexification K n).toMonoidHom

theorem isClosedEmbedding_archimedeanComplexGL :
    Topology.IsClosedEmbedding (archimedeanComplexGL K n) :=
  (isClosedEmbedding_archimedeanComplexification K n).units_map

/-- The same complex representation on the actual completion-based group. -/
def infiniteAdelicComplexGL :
    Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K) →ₜ*
      Matrix.GeneralLinearGroup (ArchimedeanComplexIndex K n) ℂ where
  __ := (archimedeanComplexGL K n).comp (archimedeanGLCoordinates K n).toMonoidHom
  continuous_toFun := (isClosedEmbedding_archimedeanComplexGL K n).continuous.comp
    (archimedeanGLCoordinates K n).continuous

@[simp]
theorem infiniteAdelicComplexGL_val
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)) :
    (infiniteAdelicComplexGL K n g).val =
      archimedeanComplexification K n (archimedeanGLCoordinates K n g).val := rfl

theorem isClosedEmbedding_infiniteAdelicComplexGL :
    Topology.IsClosedEmbedding (infiniteAdelicComplexGL K n) :=
  (isClosedEmbedding_archimedeanComplexGL K n).comp
    (archimedeanGLCoordinates K n).toHomeomorph.isClosedEmbedding

/-- The squared entry norm is the sum of the squared norms at all infinite places. -/
theorem archimedeanComplexification_sum_sq (A : ArchimedeanMatrix K n) :
    (∑ i, ∑ j, ‖archimedeanComplexification K n A i j‖ ^ 2) =
      (∑ v : {v : InfinitePlace K // IsReal v}, ∑ i, ∑ j, ‖(A i j).1 v‖ ^ 2) +
      (∑ v : {v : InfinitePlace K // IsComplex v}, ∑ i, ∑ j, ‖(A i j).2 v‖ ^ 2) := by
  simp only [Fintype.sum_prod_type, archimedeanComplexification_apply]
  simp only [apply_ite norm, norm_zero, ite_pow, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  simp [Fintype.sum_sum_type, archimedeanPlaceEmbedding]

/-- The local-coordinate sum formula on the actual completion-based group. -/
theorem infiniteAdelicComplexGL_sum_sq
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)) :
    (∑ i, ∑ j, ‖(infiniteAdelicComplexGL K n g).val i j‖ ^ 2) =
      (∑ v : {v : InfinitePlace K // IsReal v}, ∑ i, ∑ j,
        ‖ArchimedeanGL.realMatrix K n (archimedeanGLCoordinates K n g) v i j‖ ^ 2) +
      (∑ v : {v : InfinitePlace K // IsComplex v}, ∑ i, ∑ j,
        ‖ArchimedeanGL.complexMatrix K n (archimedeanGLCoordinates K n g) v i j‖ ^ 2) :=
  archimedeanComplexification_sum_sq K n _

/-- Orthogonal real blocks and unitary complex blocks give a unitary complex matrix. -/
theorem archimedeanComplexGL_mem_unitaryGroup (g : ArchimedeanGL K n)
    (hr : ∀ v, ArchimedeanGL.realMatrix K n g v ∈ Matrix.unitaryGroup (Fin n) ℝ)
    (hc : ∀ v, ArchimedeanGL.complexMatrix K n g v ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (archimedeanComplexGL K n g).val ∈ Matrix.unitaryGroup (ArchimedeanComplexIndex K n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  change Matrix.blockDiagonal (archimedeanLocalMatrices K n g.val) *
    (Matrix.blockDiagonal (archimedeanLocalMatrices K n g.val)).conjTranspose = 1
  rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul,
    ← Matrix.blockDiagonal_one]
  congr 1
  funext v
  cases v with
  | inl v =>
    have h := (realMatrix_mem_unitary_iff n _).mp (hr v)
    have he : ((ArchimedeanGL.realMatrix K n g v).map Complex.ofReal).conjTranspose =
        (ArchimedeanGL.realMatrix K n g v).transpose.map Complex.ofReal := by
      ext i j
      simp
    change (ArchimedeanGL.realMatrix K n g v).map Complex.ofReal *
      ((ArchimedeanGL.realMatrix K n g v).map Complex.ofReal).conjTranspose = 1
    rw [he]
    change (Complex.ofRealHom.mapMatrix) _ * (Complex.ofRealHom.mapMatrix) _ = 1
    rw [← map_mul, h, map_one]
  | inr v =>
    exact (Matrix.mem_unitaryGroup_iff.mp (hc v))

/-- The published standard infinite compact acts unitarily in complex coordinates. -/
theorem infiniteAdelicComplexGL_mem_unitaryGroup
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K))
    (hg : g ∈ standardInfiniteCompact K n) :
    (infiniteAdelicComplexGL K n g).val ∈
      Matrix.unitaryGroup (ArchimedeanComplexIndex K n) ℂ := by
  obtain ⟨hr, hc⟩ := (mem_standardInfiniteCompact_iff K n g).mp hg
  exact archimedeanComplexGL_mem_unitaryGroup K n _ hr hc

end Langlands.Global
