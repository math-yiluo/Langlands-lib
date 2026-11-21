import Langlands.LinearAlgebra.CliffordSpinLift
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # Clifford products of unit-vector reflections over coefficient rings -/

noncomputable section

universe u v w

namespace Langlands.QuadraticForm

open CliffordAlgebra QuadraticMap Matrix

variable {A : Type u} {V : Type v} [CommRing A] [AddCommGroup V] [Module A V]
  (Q : QuadraticForm A V)

private def unitReflectionLinear (v : V) : V →ₗ[A] V :=
  LinearMap.id - (Q.polarBilin v).smulRight v

private theorem unitReflectionLinear_apply (v x : V) :
    unitReflectionLinear Q v x = x - polar Q v x • v := rfl

/-- The linear reflection along a vector of quadratic value one works over any
commutative coefficient ring. -/
def unitReflection (v : V) (hv : Q v = 1) : V ≃ₗ[A] V :=
  LinearEquiv.ofInvolutive (unitReflectionLinear Q v) (by
    intro x
    simp only [unitReflectionLinear_apply, polar_sub_right, polar_smul_right,
      polar_self, hv, two_smul, smul_eq_mul, ← two_mul, mul_one]
    have h : polar Q v x - polar Q v x * 2 = -polar Q v x := by ring
    rw [h, neg_smul, sub_neg_eq_add, sub_add_cancel])

@[simp] theorem unitReflection_apply (v : V) (hv : Q v = 1) (x : V) :
    unitReflection Q v hv x = x - polar Q v x • v := rfl

/-- The unit-vector reflection has determinant minus one on a finite free module. -/
theorem det_unitReflection {ι : Type w} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι A V)
    (v : V) (hv : Q v = 1) : LinearEquiv.det (unitReflection Q v hv) = -1 := by
  apply Units.ext
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix b]
  let x : ι → A := fun i => b.repr v i
  let y : ι → A := fun i => polar Q v (b i)
  have hmat : LinearMap.toMatrix b b (unitReflection Q v hv).toLinearMap =
      1 + replicateCol PUnit.{1} (-x) * replicateRow PUnit.{1} y := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    change b.repr (unitReflection Q v hv (b j)) i = _
    have hleft : b.repr (unitReflection Q v hv (b j)) = Finsupp.single j 1 - y j • b.repr v := by
      rw [unitReflection_apply, map_sub, map_smul, b.repr_self]
    have hi := congrArg (fun p : ι →₀ A => p i) hleft
    rw [hi, Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.single_apply, Matrix.add_apply,
      Matrix.one_apply, Matrix.mul_apply]
    simp only [smul_eq_mul, Finset.univ_unique, Finset.sum_singleton, Matrix.replicateCol_apply,
      Matrix.replicateRow_apply, Pi.neg_apply, neg_mul, sub_eq_add_neg]
    simp only [eq_comm, mul_comm, x]
  rw [hmat, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hd : y ⬝ᵥ (-x) = -(polar Q v v) := by
    rw [dotProduct_neg, neg_inj]
    change ∑ i, polar Q v (b i) * b.repr v i = polar Q v v
    change ∑ i, Q.polarBilin v (b i) * b.repr v i = Q.polarBilin v v
    calc
      _ = ∑ i, Q.polarBilin v (b.repr v i • b i) := by
        simp only [map_smul, mul_comm, smul_eq_mul]
      _ = _ := by rw [← map_sum, b.sum_repr]
  rw [hd, polar_self, hv]
  change (1 : A) + -(2 • (1 : A)) = -1
  ring

/-- A vector of quadratic value one gives a self-inverse Clifford unit. -/
def unitVector (v : V) (hv : Q v = 1) : (CliffordAlgebra Q)ˣ where
  val := ι Q v
  inv := ι Q v
  val_inv := by rw [ι_sq_scalar, hv, map_one]
  inv_val := by rw [ι_sq_scalar, hv, map_one]

@[simp] theorem unitVector_val (v : V) (hv : Q v = 1) :
    (unitVector Q v hv : CliffordAlgebra Q) = ι Q v := rfl

private theorem unitVector_intertwines (v : V) (hv : Q v = 1) (x : V) :
    ι Q v * ι Q x = -ι Q (unitReflection Q v hv x) * ι Q v := by
  rw [unitReflection_apply, map_sub, map_smul, neg_sub, sub_mul, smul_mul_assoc,
    ι_sq_scalar, hv, map_one, ← Algebra.algebraMap_eq_smul_one, eq_sub_iff_add_eq]
  exact ι_mul_ι_add_swap v x

/-- A product of two unit Clifford vectors with its even reflection action gives a
norm-one Clifford lift over the coefficient ring. -/
def unitReflectionPair {ι : Type w} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι A V)
    (v w : V) (hv : Q v = 1) (hw : Q w = 1) : CliffordSpinLift Q := by
  refine ⟨(unitVector Q v hv * unitVector Q w hw,
    unitReflection Q v hv * unitReflection Q w hw), ?_, ?_, ?_, ?_⟩
  · change involute (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w) = _
    rw [map_mul, involute_ι, involute_ι, neg_mul_neg]
    rfl
  · change reverse (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w) *
      (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w) = 1
    rw [reverse.map_mul, reverse_ι, reverse_ι, mul_assoc,
      ← mul_assoc (CliffordAlgebra.ι Q v), ι_sq_scalar, hv, map_one, one_mul, ι_sq_scalar, hw, map_one]
  · change LinearEquiv.det (unitReflection Q v hv * unitReflection Q w hw) = 1
    rw [map_mul, det_unitReflection Q b, det_unitReflection Q b, neg_mul_neg, mul_one]
  · intro x
    change (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w) * CliffordAlgebra.ι Q x =
      CliffordAlgebra.ι Q (unitReflection Q v hv (unitReflection Q w hw x)) *
        (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w)
    rw [mul_assoc, unitVector_intertwines Q w hw, neg_mul, mul_neg,
      ← mul_assoc (CliffordAlgebra.ι Q v), unitVector_intertwines Q v hv,
      neg_mul]
    simp only [neg_mul, neg_neg, mul_assoc]

@[simp] theorem unitReflectionPair_unit {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A V) (v w : V) (hv : Q v = 1) (hw : Q w = 1) :
    (CliffordSpinLift.unit Q (unitReflectionPair Q b v w hv hw) : CliffordAlgebra Q) =
      CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w := rfl

end Langlands.QuadraticForm
