import Langlands.GroupScheme.Quaternionic.HyperbolicLevi
import Langlands.GroupScheme.Quaternionic.HyperbolicDecomposition
import Langlands.GroupScheme.Quaternionic.QuadraticValueExt
import Langlands.GroupScheme.Quaternionic.BinaryQuaternionGroupScheme

/-! # Extending binary matrices along an actual hyperbolic plane -/

noncomputable section

universe u v w w'

open Matrix

namespace Langlands.GroupScheme

namespace SplitMatrixExtension

variable {A : Type u} [Ring A] {m : Type v} {n : Type w}
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (E : Matrix m n A) (R : Matrix n m A) (h : E * R = 1)

/-- Extend a matrix on a split subspace by the identity on the complementary kernel. -/
def value (M : Matrix m m A) : Matrix n n A :=
  R * M * E + (1 - R * E)

omit [Fintype n] in
theorem value_one : value E R 1 = 1 := by
  simp [value]

include h in
/-- Matrix extension is multiplicative whenever the rectangular maps split. -/
theorem value_mul (M N : Matrix m m A) :
    value E R (M * N) = value E R M * value E R N := by
  have hQR : (1 - R * E) * R = 0 := by
    simp [Matrix.sub_mul, Matrix.mul_assoc, h]
  have hEQ : E * (1 - R * E) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h, Matrix.one_mul, sub_self]
  have hQQ : (1 - R * E) * (1 - R * E) = 1 - R * E := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hQR, Matrix.zero_mul, sub_zero]
  have hMM : (R * M * E) * (R * N * E) = R * (M * N) * E := by
    calc
      _ = R * M * (E * R) * N * E := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hMQ : (R * M * E) * (1 - R * E) = 0 := by
    rw [Matrix.mul_assoc, hEQ, Matrix.mul_zero]
  have hQM : (1 - R * E) * (R * N * E) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQR, Matrix.zero_mul, Matrix.zero_mul]
  simp only [value, Matrix.add_mul, Matrix.mul_add, hMM, hMQ, hQM, hQQ,
    add_zero, zero_add]

/-- The full matrix monoid acts on the ambient space through the split inclusion. -/
def hom : Matrix m m A →* Matrix n n A where
  toFun := value E R
  map_one' := value_one E R
  map_mul' := value_mul E R h

/-- The actual unit extension, with its inverse supplied by the matrix-monoid homomorphism. -/
def unitsHom : (Matrix m m A)ˣ →* (Matrix n n A)ˣ :=
  Units.map (hom E R h)

@[simp] theorem unitsHom_val (g : (Matrix m m A)ˣ) :
    (unitsHom E R h g : Matrix n n A) = value E R g := rfl

include h in
/-- Restricting the extended matrix to the split subspace recovers every entry. -/
theorem recover (M : Matrix m m A) : E * value E R M * R = M := by
  calc
    _ = (E * R) * M * (E * R) + (E * R - (E * R) * (E * R)) := by
      simp only [value, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_one, Matrix.mul_assoc]
    _ = M := by rw [h]; simp

theorem unitsHom_injective : Function.Injective (unitsHom E R h) := by
  intro g g' he
  apply Units.ext
  have hv := congrArg (fun z : (Matrix n n A)ˣ => E * (z : Matrix n n A) * R) he
  simpa only [unitsHom_val, recover E R h] using hv

omit [Fintype n] [DecidableEq m] in
/-- The extension commutes with all changes of coefficient ring. -/
theorem value_map {B : Type w'} [Ring B] (f : A →+* B) (M : Matrix m m A) :
    (value E R M).map f = value (E.map f) (R.map f) (M.map f) := by
  simp [value, Matrix.map_add, Matrix.map_sub, Matrix.map_mul]

end SplitMatrixExtension

namespace Quaternionic.FirstKindInvolution

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  (σ : FirstKindInvolution K D) {n : Type w} [Fintype n] [DecidableEq n]
  (q : σ.QuadraticForms n) (e f : n → D)

/-- The two rows of the actual hyperbolic plane. -/
def planeInclusion : Matrix (Fin 2) n D := ![e, f]

/-- Polar coordinates retract the ambient rows to the hyperbolic plane. -/
def planeRetraction : Matrix n (Fin 2) D :=
  fun i j => if j = 0 then (σ.polar q *ᵥ (σ ∘ f)) i else
    (σ.polar q *ᵥ (σ ∘ e)) i

omit [Fintype n] [DecidableEq n] in
theorem vecMul_planeInclusion (v : Fin 2 → D) :
    v ᵥ* planeInclusion e f = v 0 • e + v 1 • f := by
  ext i
  simp [planeInclusion, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem vecMul_planeRetraction (v : n → D) :
    v ᵥ* planeRetraction σ q e f =
      ![σ.sesqForm (σ.polar q) v f, σ.sesqForm (σ.polar q) v e] := by
  ext i
  fin_cases i <;>
    simp [planeRetraction, Matrix.vecMul, dotProduct, σ.sesqForm_eq_dotProduct]

variable {σ q e f}

namespace IsHyperbolicPair

variable (h : σ.IsHyperbolicPair q e f)

include h in
theorem planeInclusion_mul_retraction :
    planeInclusion e f * planeRetraction σ q e f = 1 := by
  ext i j
  change ((planeInclusion e f i) ᵥ* planeRetraction σ q e f) j = _
  rw [vecMul_planeRetraction]
  fin_cases i <;> fin_cases j <;>
    simp [planeInclusion, h.2.2, h.symm.2.2,
      sesqForm_polar_self_eq_zero σ q e h.1,
      sesqForm_polar_self_eq_zero σ q f h.2.1]

/-- The actual binary-unit extension into the ambient matrix-unit group. -/
def planeUnitsHom : (Matrix (Fin 2) (Fin 2) D)ˣ →* (Matrix n n D)ˣ :=
  SplitMatrixExtension.unitsHom (planeInclusion e f) (planeRetraction σ q e f)
    h.planeInclusion_mul_retraction

theorem planeUnitsHom_injective : Function.Injective h.planeUnitsHom :=
  SplitMatrixExtension.unitsHom_injective _ _ _

/-- The extension acts by the given binary matrix on the plane and fixes the remainder. -/
theorem vecMul_planeUnitsHom (g : (Matrix (Fin 2) (Fin 2) D)ˣ) (v : n → D) :
    v ᵥ* (h.planeUnitsHom g : Matrix n n D) =
      ((v ᵥ* planeRetraction σ q e f) ᵥ* (g : Matrix (Fin 2) (Fin 2) D)) ᵥ*
        planeInclusion e f + σ.hyperbolicRemainder q e f v := by
  change v ᵥ* SplitMatrixExtension.value (planeInclusion e f)
    (planeRetraction σ q e f) g = _
  rw [SplitMatrixExtension.value, Matrix.vecMul_add, Matrix.vecMul_sub,
    Matrix.vecMul_one, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
    ← Matrix.vecMul_vecMul, vecMul_planeRetraction, vecMul_planeInclusion,
    hyperbolicRemainder_apply, hyperbolicProjection_apply]
  simp only [vecMul_planeInclusion, Matrix.cons_val_zero, Matrix.cons_val_one]

include h in
/-- The pulled-back quadratic class is the canonical binary hyperbolic class. -/
theorem quadraticPullback_planeInclusion :
    σ.quadraticPullback (planeInclusion e f) q = BinaryScheme.hyperbolicForm σ := by
  apply σ.quadraticValue_ext
  intro v
  rw [quadraticValue_quadraticPullback, vecMul_planeInclusion, h.quadraticValue_plane]
  simp [BinaryScheme.hyperbolicForm, BinaryAction.hyperbolicMatrix,
    quadraticValue_mk, sesqForm, Fin.sum_univ_two]

end IsHyperbolicPair

end Quaternionic.FirstKindInvolution

end Langlands.GroupScheme
