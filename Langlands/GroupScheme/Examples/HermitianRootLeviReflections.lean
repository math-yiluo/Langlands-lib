import Langlands.GroupScheme.Examples.HermitianRootReflections

/-! # Elementary lifts of Hermitian middle reflections -/

namespace Langlands.GroupScheme.HermitianRoot

open SU3Root

universe u v

variable {L : Type u} {ι : Type v}
  [Field L] [Fintype ι] {c : RingInvolution L}

namespace Parameters

/-- A trace-zero scalar with zero vector gives a central root parameter. -/
abbrev traceZero (H : DiagonalForm c ι) (s : L) (hs : s + c.bar s = 0) :
    Parameters H :=
  ⟨(0, s), by simpa using hs⟩

@[simp] theorem traceZero_vector (H : DiagonalForm c ι) (s : L)
    (hs : s + c.bar s = 0) : (traceZero H s hs).vector = 0 := rfl

@[simp] theorem traceZero_scalar (H : DiagonalForm c ι) (s : L)
    (hs : s + c.bar s = 0) : (traceZero H s hs).scalar = s := rfl

end Parameters

variable [DecidableEq ι] {H : DiagonalForm c ι}

/-- A pure hyperbolic reflection, obtained from actual root factors. -/
def traceZeroReflection (H : DiagonalForm c ι) (s : L)
    (hs : s + c.bar s = 0) (hne : s ≠ 0) :
    Matrix.GeneralLinearGroup (Index ι) L :=
  reflectionElement (Parameters.traceZero H s hs) hne

theorem traceZeroReflection_val (H : DiagonalForm c ι) (s : L)
    (hs : s + c.bar s = 0) (hne : s ≠ 0) :
    (traceZeroReflection H s hs hne : Matrix (Index ι) (Index ι) L) =
      reflectionMatrix (Parameters.traceZero H s hs) :=
  reflectionElement_val (Parameters.traceZero H s hs) hne

theorem traceZeroReflection_mem_elementarySubgroup (H : DiagonalForm c ι)
    (s : L) (hs : s + c.bar s = 0) (hne : s ≠ 0) :
    traceZeroReflection H s hs hne ∈ elementarySubgroup H :=
  reflectionElement_mem_elementarySubgroup _ _

theorem traceZeroReflection_mul_conjugate (H : DiagonalForm c ι)
    (s : L) (hs : s + c.bar s = 0) (hne : s ≠ 0) :
    traceZeroReflection H s hs hne *
      traceZeroReflection H (c.bar s) (by simpa [add_comm] using hs)
        (by simpa using hne) = 1 := by
  apply Units.ext
  change
    ((traceZeroReflection H s hs hne) : Matrix (Index ι) (Index ι) L) *
      ((traceZeroReflection H (c.bar s) _ _) : Matrix (Index ι) (Index ι) L) = 1
  simp only [traceZeroReflection_val]
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [reflectionMatrix, reflectionMiddle, Parameters.traceZero_vector,
      Parameters.traceZero_scalar, Matrix.fromBlocks, Matrix.mul_apply,
      Fintype.sum_sum_type, Matrix.one_apply, hne]

theorem traceZeroReflection_inv (H : DiagonalForm c ι)
    (s : L) (hs : s + c.bar s = 0) (hne : s ≠ 0) :
    (traceZeroReflection H s hs hne)⁻¹ =
      traceZeroReflection H (c.bar s) (by simpa [add_comm] using hs)
        (by simpa using hne) :=
  (eq_inv_of_mul_eq_one_right (traceZeroReflection_mul_conjugate H s hs hne)).symm

/-- The middle Levi matrix with hyperbolic coefficients a and 1/bar(a). -/
def leviMatrix (a : L) (T : Matrix ι ι L) : Matrix (Index ι) (Index ι) L :=
  Matrix.fromBlocks (Matrix.of fun _ _ => a) 0 0
    (Matrix.fromBlocks T 0 0 (Matrix.of fun _ _ => (c.bar a)⁻¹))

/-- Cancelling a pure hyperbolic reflection lifts the middle reflection to the Levi. -/
def reflectionLeviElement (x : Parameters H) (hx : x.scalar ≠ 0)
    (s : L) (hs : s + c.bar s = 0) (hne : s ≠ 0) :
    Matrix.GeneralLinearGroup (Index ι) L :=
  reflectionElement x hx * (traceZeroReflection H s hs hne)⁻¹

theorem reflectionLeviElement_mem_elementarySubgroup (x : Parameters H)
    (hx : x.scalar ≠ 0) (s : L) (hs : s + c.bar s = 0) (hne : s ≠ 0) :
    reflectionLeviElement x hx s hs hne ∈ elementarySubgroup H :=
  (elementarySubgroup H).mul_mem
    (reflectionElement_mem_elementarySubgroup x hx)
    ((elementarySubgroup H).inv_mem
      (traceZeroReflection_mem_elementarySubgroup H s hs hne))

theorem reflectionLeviElement_val (x : Parameters H) (hx : x.scalar ≠ 0)
    (s : L) (hs : s + c.bar s = 0) (hne : s ≠ 0) :
    (reflectionLeviElement x hx s hs hne : Matrix (Index ι) (Index ι) L) =
      leviMatrix (c := c) (x.scalar / s) (reflectionMiddle x) := by
  have hbar : c.bar x.scalar ≠ 0 := by simpa using hx
  change (reflectionElement x hx : Matrix (Index ι) (Index ι) L) *
    (((traceZeroReflection H s hs hne)⁻¹ :
      Matrix.GeneralLinearGroup (Index ι) L) : Matrix (Index ι) (Index ι) L) = _
  rw [traceZeroReflection_inv]
  rw [reflectionElement_val, traceZeroReflection_val]
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [reflectionMatrix, reflectionMiddle, leviMatrix, Matrix.fromBlocks,
      Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, map_div₀] <;> ring

theorem diagonalEmbedding_mem_elementarySubgroup_of_traceZero
    (H : DiagonalForm c ι) (s : L) (hs : s + c.bar s = 0) (hne : s ≠ 0)
    (r : Lˣ) (hr : c.bar (r : L) = r) :
    diagonalEmbedding r ∈ elementarySubgroup H := by
  have hrs : (r : L) * s + c.bar ((r : L) * s) = 0 := by
    rw [map_mul, hr]
    linear_combination (r : L) * hs
  have hne' : (r : L) * s ≠ 0 := mul_ne_zero r.ne_zero hne
  have h := reflectionLeviElement_mem_elementarySubgroup
    (Parameters.traceZero H ((r : L) * s) hrs) hne' s hs hne
  have heq : reflectionLeviElement
      (Parameters.traceZero H ((r : L) * s) hrs) hne' s hs hne =
        diagonalEmbedding (ι := ι) r := by
    apply Units.ext
    rw [reflectionLeviElement_val (Parameters.traceZero H ((r : L) * s) hrs)
      hne' s hs hne, diagonalEmbedding_val]
    ext i j
    rcases i with i | i | i <;> rcases j with j | j | j <;>
      simp [leviMatrix, reflectionMiddle, diagonalMatrix, diagonalWeight,
        Matrix.fromBlocks, Matrix.diagonal_apply, Matrix.one_apply, hr, hne]
  rwa [heq] at h

end Langlands.GroupScheme.HermitianRoot
