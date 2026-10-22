import Langlands.Global.ArchimedeanGL
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Algebra.Star.Unitary

noncomputable section

/-!
# Standard compact subgroup at the infinite places

Actual real orthogonal and complex unitary matrix groups are assembled in mixed
coordinates, then transported to the archimedean completions. Compactness is
proved from closedness and entrywise bounds; maximality is not asserted here.
-/

universe u

namespace Langlands.Global

open NumberField NumberField.InfinitePlace

/-- The unitary matrix group is compact in its entrywise topology. -/
theorem isCompact_unitaryMatrix (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) :
    IsCompact (Matrix.unitaryGroup (Fin n) 𝕜 : Set (Matrix (Fin n) (Fin n) 𝕜)) := by
  apply (isCompact_closedBall (0 : 𝕜) 1).matrix.of_isClosed_subset isClosed_unitary
  intro U hU i j
  exact mem_closedBall_zero_iff.mpr (entry_norm_bound_of_unitary hU i j)

instance compactSpace_unitaryMatrix (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) :
    CompactSpace (Matrix.unitaryGroup (Fin n) 𝕜) :=
  isCompact_iff_compactSpace.mp (isCompact_unitaryMatrix 𝕜 n)

/-- Over the reals the unitary condition is precisely orthogonality. -/
theorem realMatrix_mem_unitary_iff (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    A ∈ Matrix.unitaryGroup (Fin n) ℝ ↔ A * A.transpose = 1 := by
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    using (Matrix.mem_unitaryGroup_iff (A := A))

variable (K : Type u) [Field K] (n : ℕ)

/-- The actual product of real orthogonal and complex unitary matrix groups. -/
abbrev ArchimedeanCompactFactors :=
  ({v : InfinitePlace K // IsReal v} → Matrix.unitaryGroup (Fin n) ℝ) ×
    ({v : InfinitePlace K // IsComplex v} → Matrix.unitaryGroup (Fin n) ℂ)

namespace ArchimedeanCompactFactors

private def matrix (p : ArchimedeanCompactFactors K n) : ArchimedeanMatrix K n :=
  fun i j => (fun v => p.1 v i j, fun v => p.2 v i j)

private theorem matrix_mul (p q : ArchimedeanCompactFactors K n) :
    matrix K n (p * q) = matrix K n p * matrix K n q := by
  apply Matrix.ext
  intro i j
  apply Prod.ext
  · funext v
    change _ = (RingHom.fst _ _) (∑ k, matrix K n p i k * matrix K n q k j) v
    rw [map_sum, Finset.sum_apply]
    rfl
  · funext v
    change _ = (RingHom.snd _ _) (∑ k, matrix K n p i k * matrix K n q k j) v
    rw [map_sum, Finset.sum_apply]
    rfl

private theorem matrix_one : matrix K n 1 = 1 := by
  apply Matrix.ext
  intro i j
  apply Prod.ext
  · funext v
    simp [matrix, Matrix.one_apply]
    split_ifs <;> rfl
  · funext v
    simp [matrix, Matrix.one_apply]
    split_ifs <;> rfl

/-- Assemble each real and complex matrix, including its inverse, in mixed coordinates. -/
def toArchimedeanGL : ArchimedeanCompactFactors K n →* ArchimedeanGL K n where
  toFun p :=
    { val := matrix K n p
      inv := matrix K n p⁻¹
      val_inv := by rw [← matrix_mul, mul_inv_cancel, matrix_one]
      inv_val := by rw [← matrix_mul, inv_mul_cancel, matrix_one] }
  map_one' := Units.ext (matrix_one K n)
  map_mul' p q := Units.ext (matrix_mul K n p q)

@[simp]
theorem toArchimedeanGL_apply (p : ArchimedeanCompactFactors K n) (i j : Fin n) :
    toArchimedeanGL K n p i j = (fun v => p.1 v i j, fun v => p.2 v i j) := rfl

theorem continuous_toArchimedeanGL : Continuous (toArchimedeanGL K n) := by
  rw [Units.continuous_iff]
  have hm : Continuous (matrix K n) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    apply Continuous.prodMk
    · apply continuous_pi
      intro v
      have hv : Continuous (fun p : ArchimedeanCompactFactors K n => (p.1 v).val) :=
        continuous_subtype_val.comp ((continuous_apply v).comp continuous_fst)
      exact (continuous_apply j).comp ((continuous_apply i).comp hv)
    · apply continuous_pi
      intro v
      have hv : Continuous (fun p : ArchimedeanCompactFactors K n => (p.2 v).val) :=
        continuous_subtype_val.comp ((continuous_apply v).comp continuous_snd)
      exact (continuous_apply j).comp ((continuous_apply i).comp hv)
  exact ⟨hm, hm.comp continuous_inv⟩

theorem toArchimedeanGL_injective : Function.Injective (toArchimedeanGL K n) := by
  intro p q h
  apply Prod.ext
  · funext v
    apply Matrix.UnitaryGroup.ext
    intro i j
    exact congrArg (fun g : ArchimedeanGL K n => (g i j).1 v) h
  · funext v
    apply Matrix.UnitaryGroup.ext
    intro i j
    exact congrArg (fun g : ArchimedeanGL K n => (g i j).2 v) h

/-- The same matrices in the actual archimedean completions. -/
def toInfiniteAdelicGL : ArchimedeanCompactFactors K n →ₜ*
    Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K) where
  __ := (archimedeanGLCoordinates K n).symm.toMonoidHom.comp (toArchimedeanGL K n)
  continuous_toFun := (archimedeanGLCoordinates K n).symm.continuous.comp
    (continuous_toArchimedeanGL K n)

@[simp]
theorem coordinates_toInfiniteAdelicGL (p : ArchimedeanCompactFactors K n) :
    archimedeanGLCoordinates K n (toInfiniteAdelicGL K n p) = toArchimedeanGL K n p :=
  (archimedeanGLCoordinates K n).apply_symm_apply _

theorem toInfiniteAdelicGL_injective : Function.Injective (toInfiniteAdelicGL K n) :=
  (archimedeanGLCoordinates K n).symm.injective.comp (toArchimedeanGL_injective K n)

end ArchimedeanCompactFactors

/-- The standard orthogonal/unitary compact subgroup in completion coordinates. -/
def standardInfiniteCompact : Subgroup
    (Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)) :=
  (ArchimedeanCompactFactors.toInfiniteAdelicGL K n).toMonoidHom.range

theorem isCompact_standardInfiniteCompact :
    IsCompact (standardInfiniteCompact K n : Set
      (Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K))) :=
  isCompact_range (ArchimedeanCompactFactors.toInfiniteAdelicGL K n).continuous

theorem isClosed_standardInfiniteCompact :
    IsClosed (standardInfiniteCompact K n : Set
      (Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K))) :=
by
  have : T2Space (InfiniteAdeleRing K) :=
    inferInstanceAs (T2Space ((v : InfinitePlace K) → v.Completion))
  exact (isCompact_standardInfiniteCompact K n).isClosed

instance compactSpace_standardInfiniteCompact : CompactSpace (standardInfiniteCompact K n) :=
  isCompact_iff_compactSpace.mp (isCompact_standardInfiniteCompact K n)


namespace ArchimedeanGL

/-- The matrix at a real place in mixed coordinates. -/
def realMatrix (g : ArchimedeanGL K n) (v : {v : InfinitePlace K // IsReal v}) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => (g i j).1 v

/-- The matrix at a complex place in mixed coordinates. -/
def complexMatrix (g : ArchimedeanGL K n) (v : {v : InfinitePlace K // IsComplex v}) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => (g i j).2 v

end ArchimedeanGL

/-- Membership is exactly orthogonality at real places and unitarity at complex places. -/
theorem mem_standardInfiniteCompact_iff
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)) :
    g ∈ standardInfiniteCompact K n ↔
      (∀ v, ArchimedeanGL.realMatrix K n (archimedeanGLCoordinates K n g) v ∈
        Matrix.unitaryGroup (Fin n) ℝ) ∧
      (∀ v, ArchimedeanGL.complexMatrix K n (archimedeanGLCoordinates K n g) v ∈
        Matrix.unitaryGroup (Fin n) ℂ) := by
  constructor
  · rintro ⟨p, rfl⟩
    have he : archimedeanGLCoordinates K n
        ((ArchimedeanCompactFactors.toInfiniteAdelicGL K n).toMonoidHom p) =
        ArchimedeanCompactFactors.toArchimedeanGL K n p :=
      ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL K n p
    rw [he]
    exact ⟨fun v => (p.1 v).property, fun v => (p.2 v).property⟩
  · rintro ⟨hr, hc⟩
    let p : ArchimedeanCompactFactors K n :=
      (fun v => ⟨ArchimedeanGL.realMatrix K n (archimedeanGLCoordinates K n g) v, hr v⟩,
       fun v => ⟨ArchimedeanGL.complexMatrix K n (archimedeanGLCoordinates K n g) v, hc v⟩)
    refine ⟨p, ?_⟩
    apply (archimedeanGLCoordinates K n).injective
    have he : archimedeanGLCoordinates K n
        ((ArchimedeanCompactFactors.toInfiniteAdelicGL K n).toMonoidHom p) =
        ArchimedeanCompactFactors.toArchimedeanGL K n p :=
      ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL K n p
    rw [he]
    apply Units.ext
    rfl

end Langlands.Global
