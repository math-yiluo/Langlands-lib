import Langlands.GroupScheme.Quaternionic.QuadraticHyperbolicSplitTorus
import Langlands.GroupScheme.Quaternionic.ScalarInvolution
import Langlands.Algebra.ReducedNormFiniteChart
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # Reduced norm of scalar hyperbolic scaling families -/

noncomputable section

universe u

open scoped Matrix TensorProduct

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K : Type u} [Field K] {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The reduced norm of a rank-one update in a scalar matrix algebra is the
usual determinant-lemma expression, over any coefficient algebra. -/
theorem reducedNorm_one_add_tmul_rankOne (R : Type u) [CommRing R] [Algebra K R]
    (a : R) (f : (n → K) →ₗ[K] K) (x : n → K) :
    CentralSimple.reducedNorm K (Matrix n n K) R
      (1 + a ⊗ₜ[K] (f.smulRight x).toMatrixRight') =
        1 + a * algebraMap K R (f x) := by
  rw [CentralSimple.reducedNorm_eq_det_fintype K (Matrix n n K)
    (Algebra.TensorProduct.lid K (Matrix n n K)) R]
  rw [_root_.map_add, _root_.map_one, ReducedNorm.splittingMap_tmul]
  simp only [Algebra.TensorProduct.lid_tmul, one_smul]
  let c : n → K := fun i => f (Pi.single i 1)
  have hM : a • ((f.smulRight x).toMatrixRight').map (algebraMap K R) =
      Matrix.replicateCol Unit (fun i => a * algebraMap K R (c i)) *
        Matrix.replicateRow Unit (fun i => algebraMap K R (x i)) := by
    ext i j
    simp [LinearMap.toMatrixRight', c, Matrix.mul_apply, Matrix.smul_apply,
      Matrix.replicateCol, Matrix.replicateRow, mul_assoc]
    change a * algebraMap K R (f (Pi.single i 1) * x j) = _
    rw [_root_.map_mul]
  rw [hM, Matrix.det_one_add_replicateCol_mul_replicateRow]
  congr 1
  rw [LinearMap.pi_apply_eq_sum_univ f x, _root_.map_sum, Finset.mul_sum]
  simp only [dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (Pi.single i 1 : n → K) = (fun j => if i = j then 1 else 0) := by
    funext j
    simp [Pi.single_apply, eq_comm]
  simp only [smul_eq_mul, _root_.map_mul, c, hi]
  ring

variable {q : (scalar K).QuadraticForms n} {x y : n → K}

/-- Each polar line projector of a scalar hyperbolic pair has reduced norm
`1+a` after the rank-one update `1+aP`, for every coefficient algebra. -/
theorem IsHyperbolicPair.reducedNorm_one_add_tmul_lineMatrix
    (h : (scalar K).IsHyperbolicPair q x y)
    (R : Type u) [CommRing R] [Algebra K R] (a : R) :
    CentralSimple.reducedNorm K (Matrix n n K) R
      (1 + a ⊗ₜ[K] (scalar K).hyperbolicLineMatrix q x y) = 1 + a := by
  rw [hyperbolicLineMatrix, reducedNorm_one_add_tmul_rankOne]
  change 1 + a * algebraMap K R ((scalar K).sesqForm ((scalar K).polar q) x y) = _
  rw [h.2.2, _root_.map_one, mul_one]

/-- Simultaneously scaling the two lines of a scalar hyperbolic pair by
`t` and `t⁻¹` has reduced norm one on every coefficient algebra. -/
theorem IsHyperbolicPair.reducedNorm_idempotentScalingValue
    (h : (scalar K).IsHyperbolicPair q x y)
    (R : Type u) [CommRing R] [Algebra K R] (t : Rˣ) :
    CentralSimple.reducedNorm K (Matrix n n K) R
      (FiniteAlgebraUnits.idempotentScalingValue (K := K)
        ((scalar K).hyperbolicLineMatrix q x y)
        ((scalar K).hyperbolicLineMatrix q y x) R t) = 1 := by
  let p := (scalar K).hyperbolicLineMatrix q x y
  let p' := (scalar K).hyperbolicLineMatrix q y x
  have hp : p * p' = 0 := h.hyperbolicLineMatrix_mul_swap
  have hfactor : FiniteAlgebraUnits.idempotentScalingValue (K := K) p p' R t =
      (1 + ((t : R) - 1) ⊗ₜ[K] p) *
        (1 + ((((t⁻¹ : Rˣ) : R)) - 1) ⊗ₜ[K] p') := by
    simp only [FiniteAlgebraUnits.idempotentScalingValue, add_mul, mul_add, one_mul,
      mul_one, Algebra.TensorProduct.tmul_mul_tmul, hp, TensorProduct.tmul_zero, add_zero,
      TensorProduct.smul_tmul', smul_eq_mul]
  rw [hfactor, _root_.map_mul, h.reducedNorm_one_add_tmul_lineMatrix,
    h.symm.reducedNorm_one_add_tmul_lineMatrix]
  simpa only [add_sub_cancel] using Units.mul_inv t

variable {I : Type u} [Fintype I] [DecidableEq I] {xs ys : I → n → K}

/-- Scaling any finite scalar hyperbolic family has reduced norm one on every
coefficient algebra, including nonreduced algebras. -/
theorem IsHyperbolicFamily.reducedNorm_familyScalingValue
    (h : (scalar K).IsHyperbolicFamily q xs ys)
    (R : Type u) [CommRing R] [Algebra K R] (t : I → Rˣ) :
    CentralSimple.reducedNorm K (Matrix n n K) R
      (FiniteAlgebraUnits.familyScalingValue (K := K)
        (fun k => (scalar K).hyperbolicLineMatrix q (xs k) (ys k))
        (fun k => (scalar K).hyperbolicLineMatrix q (ys k) (xs k)) R t) = 1 := by
  let p := fun k => (scalar K).hyperbolicLineMatrix q (xs k) (ys k)
  let p' := fun k => (scalar K).hyperbolicLineMatrix q (ys k) (xs k)
  have hs : ∀ s : Finset I, CentralSimple.reducedNorm K (Matrix n n K) R
      (1 + ∑ k ∈ s, FiniteAlgebraUnits.familyScalingSummand (K := K) p p' R t k) = 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
      have heq : 1 + ∑ k ∈ insert j s,
          FiniteAlgebraUnits.familyScalingSummand (K := K) p p' R t k =
          (1 + FiniteAlgebraUnits.familyScalingSummand (K := K) p p' R t j) *
            (1 + ∑ k ∈ s, FiniteAlgebraUnits.familyScalingSummand (K := K) p p' R t k) := by
        rw [Finset.sum_insert hj, add_mul, one_mul, mul_add, mul_one, Finset.mul_sum,
          Finset.sum_eq_zero (fun k hk => h.isOrthogonalIdempotentPairs.summand_mul_of_ne
            R t t (ne_of_mem_of_not_mem hk hj).symm), add_zero]
        abel
      rw [heq, _root_.map_mul, ih, mul_one]
      rw [FiniteAlgebraUnits.familyScalingSummand, ← add_assoc]
      exact (h.isHyperbolicPair j).reducedNorm_idempotentScalingValue R (t j)
  exact hs Finset.univ

/-- The scaling homomorphism with its codomain restricted to the actual
reduced-norm-one subgroup of matrix units. -/
def IsHyperbolicFamily.normOneScalingUnits
    (h : (scalar K).IsHyperbolicFamily q xs ys)
    (R : Type u) [CommRing R] [Algebra K R] :
    (I → Rˣ) →* CentralSimple.reducedNormOne K (Matrix n n K) R where
  toFun t :=
    ⟨h.isOrthogonalIdempotentPairs.scalingUnits R t,
      (CentralSimple.mem_reducedNormOne K (Matrix n n K) R _).2
        (h.reducedNorm_familyScalingValue R t)⟩
  map_one' := Subtype.ext (h.isOrthogonalIdempotentPairs.scalingUnits R).map_one
  map_mul' t s := Subtype.ext ((h.isOrthogonalIdempotentPairs.scalingUnits R).map_mul t s)

@[simp] theorem IsHyperbolicFamily.normOneScalingUnits_coe
    (h : (scalar K).IsHyperbolicFamily q xs ys)
    (R : Type u) [CommRing R] [Algebra K R] (t : I → Rˣ) :
    (h.normOneScalingUnits R t : (R ⊗[K] Matrix n n K)ˣ) =
      h.isOrthogonalIdempotentPairs.scalingUnits R t := rfl

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
