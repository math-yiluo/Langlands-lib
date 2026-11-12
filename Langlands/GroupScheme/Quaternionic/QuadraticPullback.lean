import Langlands.GroupScheme.Quaternionic.IsometryWeights
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Pullback of quaternionic quadratic forms

Rectangular matrices pull back the actual quotient-valued forms of `Forms`.
The construction uses the row-vector convention and works in every characteristic.
-/

noncomputable section

universe u v w w' w''

open Matrix

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  (σ : Langlands.GroupScheme.Quaternionic.FirstKindInvolution K D)
  {l : Type w} {m : Type w'} {n : Type w''}
  [Fintype l] [Fintype m] [Fintype n]
  [DecidableEq l] [DecidableEq m] [DecidableEq n]

/-- Conjugate transpose of a rectangular matrix. -/
def rectangularAdjoint (g : Matrix m n D) : Matrix n m D :=
  fun i j => σ (g j i)

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
@[simp] theorem rectangularAdjoint_apply (g : Matrix m n D) (i : n) (j : m) :
    σ.rectangularAdjoint g i j = σ (g j i) := rfl

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
@[simp] theorem rectangularAdjoint_rectangularAdjoint (g : Matrix m n D) :
    σ.rectangularAdjoint (σ.rectangularAdjoint g) = g := by
  ext i j
  simp

theorem rectangularAdjoint_square (g : Matrix n n D) :
    σ.rectangularAdjoint g = σ.matrix n g := rfl

omit [Fintype l] [Fintype n] [DecidableEq l] [DecidableEq m] [DecidableEq n] in
@[simp] theorem rectangularAdjoint_mul (g : Matrix l m D) (h : Matrix m n D) :
    σ.rectangularAdjoint (g * h) = σ.rectangularAdjoint h * σ.rectangularAdjoint g := by
  ext i j
  simp [rectangularAdjoint, Matrix.mul_apply]

/-- Pullback of Gram matrices under the row map `x ↦ x g`. -/
def gramPullback (g : Matrix m n D) : Matrix n n D →ₗ[K] Matrix m m D where
  toFun Q := g * Q * σ.rectangularAdjoint g
  map_add' Q Q' := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c Q := by simp [Matrix.mul_smul, Matrix.smul_mul]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
@[simp] theorem gramPullback_apply (g : Matrix m n D) (Q : Matrix n n D) :
    σ.gramPullback g Q = g * Q * σ.rectangularAdjoint g := rfl

/-- Pulling back a representative of zero still represents zero. -/
theorem gramPullback_mem_quadraticKernel (g : Matrix m n D) {Q : Matrix n n D}
    (hQ : Q ∈ σ.quadraticKernel n) :
    σ.gramPullback g Q ∈ σ.quadraticKernel m := by
  obtain ⟨a, rfl⟩ := (σ.matrix n).mem_alternatingSubspace.mp hQ
  apply (σ.matrix m).mem_alternatingSubspace.mpr
  refine ⟨g * a * σ.rectangularAdjoint g, ?_⟩
  change g * a * σ.rectangularAdjoint g -
    σ.rectangularAdjoint (g * a * σ.rectangularAdjoint g) =
    g * (a - σ.rectangularAdjoint a) * σ.rectangularAdjoint g
  simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

/-- Pullback of Tits's quotient-valued quadratic forms by a rectangular matrix. -/
def quadraticPullback (g : Matrix m n D) : σ.QuadraticForms n →ₗ[K] σ.QuadraticForms m :=
  (σ.quadraticKernel n).mapQ (σ.quadraticKernel m) (σ.gramPullback g)
    (fun _ hQ => σ.gramPullback_mem_quadraticKernel g hQ)

@[simp] theorem quadraticPullback_mk (g : Matrix m n D) (Q : Matrix n n D) :
    σ.quadraticPullback g (Submodule.Quotient.mk Q) =
      Submodule.Quotient.mk (g * Q * σ.rectangularAdjoint g) := rfl

@[simp] theorem quadraticPullback_one (q : σ.QuadraticForms n) :
    σ.quadraticPullback (1 : Matrix n n D) q = q := by
  induction q using Submodule.Quotient.induction_on with
  | _ Q => simp [rectangularAdjoint_square]

/-- Composition follows the order of row-matrix multiplication. -/
theorem quadraticPullback_mul (g : Matrix l m D) (h : Matrix m n D)
    (q : σ.QuadraticForms n) :
    σ.quadraticPullback (g * h) q =
      σ.quadraticPullback g (σ.quadraticPullback h q) := by
  induction q using Submodule.Quotient.induction_on with
  | _ Q => simp [Matrix.mul_assoc]

omit [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- Conjugate transpose commutes with multiplication of a row by a matrix. -/
theorem rectangularAdjoint_mulVec (g : Matrix m n D) (x : m → D) :
    σ.rectangularAdjoint g *ᵥ (fun i => σ (x i)) =
      fun j => σ ((x ᵥ* g) j) := by
  ext j
  simp [Matrix.mulVec, Matrix.vecMul, dotProduct]

omit [DecidableEq m] [DecidableEq n] in
/-- The Gram formula agrees with evaluation on the pulled-back rows. -/
theorem sesqForm_gramPullback (g : Matrix m n D) (Q : Matrix n n D) (x y : m → D) :
    σ.sesqForm (σ.gramPullback g Q) x y =
      σ.sesqForm Q (x ᵥ* g) (y ᵥ* g) := by
  rw [σ.sesqForm_eq_dotProduct, σ.sesqForm_eq_dotProduct]
  simp only [Function.comp_def]
  rw [gramPullback_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    σ.rectangularAdjoint_mulVec, Matrix.dotProduct_mulVec]

/-- Values of the quotient form agree under the actual row map. -/
theorem quadraticValue_quadraticPullback (g : Matrix m n D) (q : σ.QuadraticForms n)
    (x : m → D) :
    σ.quadraticValue x (σ.quadraticPullback g q) =
      σ.quadraticValue (x ᵥ* g) q := by
  induction q using Submodule.Quotient.induction_on with
  | _ Q =>
    simp only [quadraticPullback_mk, quadraticValue_mk]
    exact congrArg Submodule.Quotient.mk (σ.sesqForm_gramPullback g Q x x)

/-- The polar matrix pulls back by the same Gram formula. -/
theorem polar_quadraticPullback (g : Matrix m n D) (q : σ.QuadraticForms n) :
    σ.polar (σ.quadraticPullback g q) = σ.gramPullback g (σ.polar q) := by
  induction q using Submodule.Quotient.induction_on with
  | _ Q =>
    simp only [quadraticPullback_mk, polar_mk, gramPullback_apply]
    change g * Q * σ.rectangularAdjoint g +
      σ.rectangularAdjoint (g * Q * σ.rectangularAdjoint g) =
      g * (Q + σ.rectangularAdjoint Q) * σ.rectangularAdjoint g
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

/-- Totally singular subspaces are preserved by the corresponding row map. -/
theorem isTotallySingular_quadraticPullback_iff (g : Matrix m n D)
    (q : σ.QuadraticForms n) (W : Submodule D (m → D)) :
    σ.IsTotallySingular (σ.quadraticPullback g q) W ↔
      σ.IsTotallySingular q (W.map g.vecMulLinear) := by
  constructor
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact (σ.quadraticValue_quadraticPullback g q x).symm.trans (h x hx)
  · intro h x hx
    rw [σ.quadraticValue_quadraticPullback]
    exact h _ ⟨x, hx, rfl⟩

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
