import Langlands.Global.ArchimedeanComplexification
import Langlands.LinearAlgebra.InverseAdjointModel

noncomputable section

universe u

open scoped Classical Matrix.Norms.Operator

namespace Langlands.Global

open Matrix NumberField NumberField.InfinitePlace Langlands.LinearAlgebra

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The scalar, standard, and inverse-adjoint coordinates for the actual infinite group. -/
abbrev ArchimedeanHilbertIndex := InverseAdjointIndex (ArchimedeanComplexIndex K n)

/-- The standard complex Euclidean Hilbert space on these finite coordinates. -/
abbrev ArchimedeanHilbertSpace := EuclideanSpace ℂ (ArchimedeanHilbertIndex K n)

theorem finrank_archimedeanHilbertSpace :
    Module.finrank ℂ (ArchimedeanHilbertSpace K n) =
      1 + 2 * (n * Fintype.card (ArchimedeanPlaceIndex K)) := by
  simp [ArchimedeanHilbertSpace, ArchimedeanHilbertIndex, InverseAdjointIndex,
    ArchimedeanComplexIndex, finrank_euclideanSpace]
  omega

/-- The actual augmented complex representation, continuous in the completion topology. -/
def infiniteAdelicHilbertRepresentation :
    Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K) →ₜ*
      (ArchimedeanHilbertSpace K n →L[ℂ] ArchimedeanHilbertSpace K n) where
  __ := inverseAdjointRepresentation.comp (infiniteAdelicComplexGL K n).toMonoidHom
  continuous_toFun := continuous_inverseAdjointRepresentation.comp
    (infiniteAdelicComplexGL K n).continuous

/-- Coordinates of the representation in the standard orthonormal basis. -/
def infiniteAdelicHilbertMatrix
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)) :
    Matrix (ArchimedeanHilbertIndex K n) (ArchimedeanHilbertIndex K n) ℂ :=
  inverseAdjointMatrix (infiniteAdelicComplexGL K n g)

theorem infiniteAdelicHilbertRepresentation_apply
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K))
    (x : ArchimedeanHilbertSpace K n) :
    WithLp.ofLp (infiniteAdelicHilbertRepresentation K n g x) =
      infiniteAdelicHilbertMatrix K n g *ᵥ WithLp.ofLp x := rfl

/-- Closedness is in the entire endomorphism space, including singular endomorphisms. -/
theorem isClosedEmbedding_infiniteAdelicHilbertRepresentation :
    Topology.IsClosedEmbedding (infiniteAdelicHilbertRepresentation K n) :=
  isClosedEmbedding_inverseAdjointRepresentation.comp
    (isClosedEmbedding_infiniteAdelicComplexGL K n)

theorem continuous_infiniteAdelicHilbertRepresentation :
    Continuous (infiniteAdelicHilbertRepresentation K n) :=
  (infiniteAdelicHilbertRepresentation K n).continuous

theorem infiniteAdelicHilbertRepresentation_injective :
    Function.Injective (infiniteAdelicHilbertRepresentation K n) :=
  (isClosedEmbedding_infiniteAdelicHilbertRepresentation K n).injective

theorem isClosed_range_infiniteAdelicHilbertRepresentation :
    IsClosed (Set.range (infiniteAdelicHilbertRepresentation K n)) :=
  (isClosedEmbedding_infiniteAdelicHilbertRepresentation K n).isClosed_range

/-- The published standard infinite compact acts by unitary Hilbert-space operators. -/
theorem infiniteAdelicHilbertRepresentation_mem_unitary
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K))
    (hg : g ∈ standardInfiniteCompact K n) :
    infiniteAdelicHilbertRepresentation K n g ∈
      unitary (ArchimedeanHilbertSpace K n →L[ℂ] ArchimedeanHilbertSpace K n) :=
  inverseAdjointRepresentation_mem_unitary _ (infiniteAdelicComplexGL_mem_unitaryGroup K n g hg)

theorem infiniteAdelicHilbertRepresentation_inner
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K))
    (hg : g ∈ standardInfiniteCompact K n) (x y : ArchimedeanHilbertSpace K n) :
    inner ℂ (infiniteAdelicHilbertRepresentation K n g x)
      (infiniteAdelicHilbertRepresentation K n g y) = inner ℂ x y :=
  inverseAdjointRepresentation_inner _ (infiniteAdelicComplexGL_mem_unitaryGroup K n g hg) x y

/-- Sum of the squared entries of the local standard matrices, with one block per infinite place. -/
def infiniteAdelicLocalEntrySq
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)) : ℝ :=
  (∑ v : {v : InfinitePlace K // IsReal v}, ∑ i, ∑ j,
    ‖ArchimedeanGL.realMatrix K n (archimedeanGLCoordinates K n g) v i j‖ ^ 2) +
  (∑ v : {v : InfinitePlace K // IsComplex v}, ∑ i, ∑ j,
    ‖ArchimedeanGL.complexMatrix K n (archimedeanGLCoordinates K n g) v i j‖ ^ 2)

/-- The squared Hilbert-Schmidt norm, defined using the actual Hilbert adjoint and linear trace. -/
def infiniteAdelicHilbertNormSq
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)) : ℝ :=
  (LinearMap.trace ℂ (ArchimedeanHilbertSpace K n)
    (star (infiniteAdelicHilbertRepresentation K n g) *
      infiniteAdelicHilbertRepresentation K n g).toLinearMap).re

theorem infiniteAdelicHilbertNormSq_eq_generic
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)) :
    infiniteAdelicHilbertNormSq K n g =
      inverseAdjointHilbertSchmidtSq (infiniteAdelicComplexGL K n g) :=
  (inverseAdjointHilbertSchmidtSq_eq_trace _).symm

/-- The trace is the squared-entry sum in the actual orthonormal coordinates. -/
theorem infiniteAdelicHilbertNormSq_eq_sum
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)) :
    infiniteAdelicHilbertNormSq K n g =
      ∑ i, ∑ j, ‖infiniteAdelicHilbertMatrix K n g i j‖ ^ 2 :=
  infiniteAdelicHilbertNormSq_eq_generic K n g

/-- The scalar block contributes one and the remaining blocks give the forward and inverse sums. -/
theorem infiniteAdelicHilbertNormSq_eq
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)) :
    infiniteAdelicHilbertNormSq K n g =
      1 + infiniteAdelicLocalEntrySq K n g + infiniteAdelicLocalEntrySq K n g⁻¹ := by
  rw [infiniteAdelicHilbertNormSq_eq_generic, inverseAdjointHilbertSchmidtSq_eq,
    ← map_inv (infiniteAdelicComplexGL K n)]
  rw [infiniteAdelicComplexGL_sum_sq, infiniteAdelicComplexGL_sum_sq]
  rfl

theorem one_le_infiniteAdelicHilbertNormSq
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)) :
    1 ≤ infiniteAdelicHilbertNormSq K n g := by
  rw [infiniteAdelicHilbertNormSq_eq_generic]
  exact one_le_inverseAdjointHilbertSchmidtSq _

/-- The actual Hilbert-Schmidt group norm with the scalar-augmented trace normalization. -/
def infiniteAdelicHilbertNorm
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)) : ℝ :=
  Real.sqrt (infiniteAdelicHilbertNormSq K n g)

theorem infiniteAdelicHilbertNorm_eq_trace
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)) :
    infiniteAdelicHilbertNorm K n g =
      Real.sqrt ((LinearMap.trace ℂ (ArchimedeanHilbertSpace K n)
        (star (infiniteAdelicHilbertRepresentation K n g) *
          infiniteAdelicHilbertRepresentation K n g).toLinearMap).re) := rfl

theorem infiniteAdelicHilbertNorm_eq_generic
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)) :
    infiniteAdelicHilbertNorm K n g =
      inverseAdjointHilbertSchmidtNorm (infiniteAdelicComplexGL K n g) := by
  simp only [infiniteAdelicHilbertNorm, infiniteAdelicHilbertNormSq_eq_generic,
    inverseAdjointHilbertSchmidtNorm]

theorem infiniteAdelicHilbertNorm_sq
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)) :
    infiniteAdelicHilbertNorm K n g ^ 2 =
      1 + infiniteAdelicLocalEntrySq K n g + infiniteAdelicLocalEntrySq K n g⁻¹ := by
  rw [infiniteAdelicHilbertNorm,
    Real.sq_sqrt (le_trans zero_le_one (one_le_infiniteAdelicHilbertNormSq K n g)),
    infiniteAdelicHilbertNormSq_eq]

theorem one_le_infiniteAdelicHilbertNorm
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)) :
    1 ≤ infiniteAdelicHilbertNorm K n g :=
  Real.one_le_sqrt.mpr (one_le_infiniteAdelicHilbertNormSq K n g)

theorem infiniteAdelicHilbertNorm_pos
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)) :
    0 < infiniteAdelicHilbertNorm K n g :=
  lt_of_lt_of_le zero_lt_one (one_le_infiniteAdelicHilbertNorm K n g)

theorem continuous_infiniteAdelicHilbertNorm :
    Continuous (infiniteAdelicHilbertNorm K n) := by
  have h := continuous_inverseAdjointHilbertSchmidtNorm.comp
    (infiniteAdelicComplexGL K n).continuous
  exact h.congr fun g => (infiniteAdelicHilbertNorm_eq_generic K n g).symm

@[simp]
theorem infiniteAdelicHilbertNorm_inv
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)) :
    infiniteAdelicHilbertNorm K n g⁻¹ = infiniteAdelicHilbertNorm K n g := by
  simp only [infiniteAdelicHilbertNorm, infiniteAdelicHilbertNormSq_eq, inv_inv]
  congr 1
  ring

@[simp]
theorem infiniteAdelicHilbertNorm_rank_zero
    (g : Matrix.GeneralLinearGroup (Fin 0) (InfiniteAdeleRing K)) :
    infiniteAdelicHilbertNorm K 0 g = 1 := by
  simp [infiniteAdelicHilbertNorm, infiniteAdelicHilbertNormSq_eq,
    infiniteAdelicLocalEntrySq]

end Langlands.Global
