import Langlands.GroupScheme.Examples.HermitianRootRationalPoints

/-! # Normal generation by the actual Hermitian upper rational points -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HermitianRoot

open SU3Root

section Parameters

variable {A : Type u} {Middle : Type v} [CommRing A] [Fintype Middle]
  {c : RingInvolution A} {H : DiagonalForm c Middle}

/-- Scaling a Hermitian vector by r scales its scalar coordinate by r times bar(r). -/
def Parameters.normScale (r : A) : Parameters H →* Parameters H where
  toFun x := ⟨(fun i => r * x.vector i, (r * c.bar r) * x.scalar), by
    change (r * c.bar r) * x.scalar + c.bar ((r * c.bar r) * x.scalar) =
      H.pairing (fun i => r * x.vector i) (fun i => r * x.vector i)
    rw [map_mul, map_mul, RingInvolution.bar_bar, DiagonalForm.pairing_scale]
    linear_combination (r * c.bar r) * x.equation⟩
  map_one' := by
    apply Parameters.ext
    · funext i
      exact mul_zero r
    · exact mul_zero _
  map_mul' x y := by
    apply Parameters.ext
    · funext i
      exact mul_add r _ _
    · change (r * c.bar r) *
          (x.scalar + y.scalar + H.pairing x.vector y.vector) =
        (r * c.bar r) * x.scalar + (r * c.bar r) * y.scalar +
          H.pairing (fun i => r * x.vector i) (fun i => r * y.vector i)
      rw [DiagonalForm.pairing_scale]
      ring

@[simp] theorem Parameters.vector_normScale (r : A) (x : Parameters H) :
    (Parameters.normScale r x).vector = fun i => r * x.vector i := rfl

@[simp] theorem Parameters.scalar_normScale (r : A) (x : Parameters H) :
    (Parameters.normScale r x).scalar = (r * c.bar r) * x.scalar := rfl

end Parameters

section Matrices

variable {L : Type u} {Middle : Type v} [Field L] [Fintype Middle] [DecidableEq Middle]
  {c : RingInvolution L} (H : DiagonalForm c Middle)

/-- An actual determinant-one pure reflection takes a rescaled upper point to
the prescribed opposite point. -/
theorem traceZeroReflection_conjugate_embedding (s : L)
    (hs : s + c.bar s = 0) (hne : s ≠ 0) (x : Parameters H) :
    traceZeroReflection H s hs hne *
        Parameters.embedding H (Parameters.normScale (c.bar s) x) *
          (traceZeroReflection H s hs hne)⁻¹ =
      oppositeEmbedding H x := by
  have hbar : c.bar s ≠ 0 := by simpa using hne
  rw [traceZeroReflection_inv]
  apply Units.ext
  change
    ((traceZeroReflection H s hs hne : Matrix.GeneralLinearGroup (Index Middle) L) :
        Matrix (Index Middle) (Index Middle) L) *
      Parameters.matrix (Parameters.normScale (c.bar s) x) *
        ((traceZeroReflection H (c.bar s) _ _ :
          Matrix.GeneralLinearGroup (Index Middle) L) :
            Matrix (Index Middle) (Index Middle) L) = _
  simp only [traceZeroReflection_val]
  ext i j
  rw [oppositeEmbedding_apply]
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [reflectionMatrix, reflectionMiddle, Parameters.traceZero_vector,
      Parameters.traceZero_scalar, Parameters.matrix, Parameters.vector_normScale,
      Parameters.scalar_normScale, swapIndex, Matrix.fromBlocks, Matrix.mul_apply,
      Fintype.sum_sum_type, Matrix.one_apply, hne, hbar, mul_assoc, mul_comm, mul_left_comm]

end Matrices

namespace SchemeModel

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]
  {Middle : Type} [Fintype Middle] [DecidableEq Middle]
  (H : DiagonalForm (fieldInvolution k L) Middle)
  (w : Middle → Lˣ) (hw : ∀ i, (w i : L) = H.weight i)

/-- The actual rational point represented by a pure determinant-one reflection. -/
def weylPoint (s : L) (hs : s + (fieldInvolution k L).bar s = 0) (hne : s ≠ 0) :
    rationalPoints (groupScheme k L H w hw) :=
  (rationalMatrixEquiv k L H w hw).symm
    ⟨traceZeroReflection H s hs hne,
      elementarySubgroup_le_specialUnitarySubgroup H
        (traceZeroReflection_mem_elementarySubgroup H s hs hne)⟩

@[simp] theorem rationalMatrixEquiv_weylPoint
    (s : L) (hs : s + (fieldInvolution k L).bar s = 0) (hne : s ≠ 0) :
    (rationalMatrixEquiv k L H w hw (weylPoint k L H w hw s hs hne)).1 =
      traceZeroReflection H s hs hne :=
  congrArg Subtype.val ((rationalMatrixEquiv k L H w hw).apply_symm_apply _)

/-- Rational pure reflection conjugation realizes every prescribed opposite point. -/
theorem weylPoint_conjugate_rationalUpper
    (s : L) (hs : s + (fieldInvolution k L).bar s = 0) (hne : s ≠ 0)
    (x : Parameters H) :
    weylPoint k L H w hw s hs hne *
        rationalUpper k L H w hw (Parameters.normScale ((fieldInvolution k L).bar s) x) *
          (weylPoint k L H w hw s hs hne)⁻¹ =
      rationalLower k L H w hw x := by
  apply (rationalMatrixEquiv k L H w hw).injective
  apply Subtype.ext
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
    rationalMatrixEquiv_weylPoint, rationalMatrixEquiv_upper, rationalMatrixEquiv_lower]
  exact traceZeroReflection_conjugate_embedding H s hs hne x

/-- A normal subgroup containing the actual upper rational family contains the
actual opposite rational family in every characteristic. -/
theorem lower_range_le_of_normal_upper_range
    (N : Subgroup (rationalPoints (groupScheme k L H w hw))) [N.Normal]
    (hu : (rationalUpper k L H w hw).range ≤ N) :
    (rationalLower k L H w hw).range ≤ N := by
  obtain ⟨a, ha⟩ := fieldInvolution_exists_nonfixed k L
  let s := a - (fieldInvolution k L).bar a
  have hs : s + (fieldInvolution k L).bar s = 0 := by
    dsimp only [s]
    simp only [map_sub, RingInvolution.bar_bar]
    ring
  have hne : s ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  rintro _ ⟨x, rfl⟩
  rw [← weylPoint_conjugate_rationalUpper k L H w hw s hs hne x]
  exact (inferInstance : N.Normal).conj_mem _ (hu ⟨_, rfl⟩) _

/-- With anisotropic middle form the actual upper rational family normally
generates the entire rational-point group. -/
theorem eq_top_of_normal_upper_range (hH : H.IsAnisotropic)
    (N : Subgroup (rationalPoints (groupScheme k L H w hw))) [N.Normal]
    (hu : (rationalUpper k L H w hw).range ≤ N) : N = ⊤ :=
  eq_top_of_rational_roots k L H w hw hH N hu
    (lower_range_le_of_normal_upper_range k L H w hw N hu)

end SchemeModel
end Langlands.GroupScheme.HermitianRoot
