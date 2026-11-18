import Langlands.GroupScheme.OddOrthogonalMatrix.Form
import Langlands.GroupScheme.OddOrthogonalMatrix.ShortMatrices
import Langlands.GroupScheme.OrthogonalMatrix.LieAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Linearized norm-one equations for the split odd quadratic form -/

noncomputable section

universe u

open scoped Matrix

namespace Langlands.GroupScheme.OddOrthogonalMatrix

variable {l : Type} [Fintype l] [DecidableEq l] {K : Type u} [Field K]

/-- The linear part of the quadratic matrix defect at the identity. -/
def lieDefect : Matrix (Index l) (Index l) K →ₗ[K] Matrix (Index l) (Index l) K where
  toFun Y := Y * formMatrix l K + formMatrix l K * Y.transpose
  map_add' Y Z := by
    simp only [add_mul, mul_add, Matrix.transpose_add]
    abel
  map_smul' c Y := by
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add,
      RingHom.id_apply]

/-- The linearized isometry and determinant-one equations. -/
def lieMatrices : Submodule K (Matrix (Index l) (Index l) K) :=
  ((Quaternionic.FirstKindInvolution.scalar K).quadraticKernel (Index l)).comap lieDefect ⊓
    LinearMap.ker (Matrix.traceLinearMap (Index l) K K)

/-- The linearized equations in ordinary alternating-matrix notation. -/
theorem mem_lieMatrices_iff (Y : Matrix (Index l) (Index l) K) :
    Y ∈ lieMatrices ↔ OrthogonalMatrix.IsAlt (lieDefect Y) ∧ Y.trace = 0 := by
  change lieDefect Y ∈ (Quaternionic.FirstKindInvolution.scalar K).quadraticKernel (Index l) ∧
    Y.trace = 0 ↔ _
  rw [Quaternionic.FirstKindInvolution.mem_quadraticKernel_scalar]
  constructor
  · rintro ⟨⟨U, hU⟩, ht⟩
    exact ⟨⟨U, hU.symm⟩, ht⟩
  · rintro ⟨⟨U, hU⟩, ht⟩
    exact ⟨⟨U, hU.symm⟩, ht⟩

/-- The hyperbolic block of an odd matrix. -/
def evenPart (Y : Matrix (Index l) (Index l) K) : Matrix (l ⊕ l) (l ⊕ l) K :=
  Y.submatrix Sum.inr Sum.inr

/-- The hyperbolic block of the linearized odd defect is the even defect. -/
theorem evenPart_lieDefect (Y : Matrix (Index l) (Index l) K) :
    evenPart (lieDefect Y) =
      evenPart Y * OrthogonalMatrix.formMatrix l K +
        OrthogonalMatrix.formMatrix l K * (evenPart Y).transpose := by
  ext i j
  simp [evenPart, lieDefect, formMatrix, Matrix.mul_apply, Fintype.sum_sum_type]

/-- A linearized odd isometry has an even orthogonal hyperbolic block. -/
theorem isAlt_evenPart_lieDefect {Y : Matrix (Index l) (Index l) K}
    (hY : OrthogonalMatrix.IsAlt (lieDefect Y)) :
    OrthogonalMatrix.IsAlt (evenPart Y * OrthogonalMatrix.formMatrix l K +
      OrthogonalMatrix.formMatrix l K * (evenPart Y).transpose) := by
  obtain ⟨U, hU⟩ := hY
  rw [← evenPart_lieDefect, hU]
  exact ⟨evenPart U, rfl⟩

/-- The even orthogonal infinitesimal condition forces trace zero without
dividing by two. -/
theorem trace_evenPart_eq_zero {Y : Matrix (Index l) (Index l) K}
    (hY : OrthogonalMatrix.IsAlt (lieDefect Y)) : (evenPart Y).trace = 0 := by
  have hE := (OrthogonalMatrix.isAlt_lie_iff _).1 (isAlt_evenPart_lieDefect hY)
  have hp : ∀ i, evenPart Y (Sum.inl i) (Sum.inl i) +
      evenPart Y (Sum.inr i) (Sum.inr i) = 0 := by
    intro i
    have h := congrFun (congrFun hE.1 (Sum.inl i)) (Sum.inr i)
    simpa [OrthogonalMatrix.polarMatrix, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.one_apply] using h
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_sum_type, ← Finset.sum_add_distrib, hp,
    Finset.sum_const_zero]

/-- The determinant equation kills the axis diagonal in every characteristic. -/
theorem axis_diagonal_eq_zero {Y : Matrix (Index l) (Index l) K}
    (hY : Y ∈ lieMatrices) : Y (Sum.inl ()) (Sum.inl ()) = 0 := by
  obtain ⟨hQ, ht⟩ := (mem_lieMatrices_iff Y).1 hY
  have he := trace_evenPart_eq_zero hQ
  have htr : Y.trace = Y (Sum.inl ()) (Sum.inl ()) + (evenPart Y).trace := by
    simp [Matrix.trace, Matrix.diag, evenPart, Fintype.sum_sum_type]
  rwa [htr, he, add_zero] at ht

/-- The axis row is determined by the axis column, with the factor two
retained in characteristic two. -/
theorem axis_row_eq {Y : Matrix (Index l) (Index l) K}
    (hY : Y ∈ lieMatrices) (a : l ⊕ l) :
    Y (Sum.inl ()) (Sum.inr a) = -2 * Y (Sum.inr a.swap) (Sum.inl ()) := by
  have h := (OrthogonalMatrix.isAlt_iff _).1 ((mem_lieMatrices_iff Y).1 hY).1
  have ha := congrFun (congrFun h.1 (Sum.inl ())) (Sum.inr a.swap)
  rcases a with a | a <;>
    simp [lieDefect, formMatrix, OrthogonalMatrix.formMatrix, Matrix.mul_apply,
      Fintype.sum_sum_type, Matrix.one_apply] at ha ⊢ <;> linear_combination ha

/-- The tangent matrix of the signed short-parameter family. -/
def shortVector (a : l ⊕ l) : Matrix (Index l) (Index l) K :=
  Matrix.single (Sum.inl ()) (Sum.inr a) (-2) +
    Matrix.single (Sum.inr a.swap) (Sum.inl ()) 1

/-- An even matrix embedded with zero axis row and column. -/
def evenEmbed (A : Matrix (l ⊕ l) (l ⊕ l) K) : Matrix (Index l) (Index l) K :=
  Matrix.fromBlocks 0 0 0 A

/-- Every solution of the linearized norm-one equations is its even block plus
a linear combination of short-family tangent matrices. -/
theorem lieMatrix_decomposition {Y : Matrix (Index l) (Index l) K}
    (hY : Y ∈ lieMatrices) :
    Y = evenEmbed (evenPart Y) +
      ∑ a : l ⊕ l, Y (Sum.inr a) (Sum.inl ()) • shortVector a.swap := by
  have hz := axis_diagonal_eq_zero hY
  have hr := axis_row_eq hY
  ext i j
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply]
  rcases i with i | i <;> rcases j with j | j
  · cases i; cases j
    simp [evenEmbed, shortVector, hz]
  · cases i
    rcases j with j | j <;> simp [evenEmbed, shortVector, Matrix.single_apply, hr, mul_comm]
  · cases j
    rcases i with i | i <;> simp [evenEmbed, shortVector, Matrix.single_apply]
  · simp [evenEmbed, evenPart, shortVector]

end Langlands.GroupScheme.OddOrthogonalMatrix
