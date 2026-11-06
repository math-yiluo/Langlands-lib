import Langlands.Algebra.MatrixAlgEquivInnerProof
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-! The determinant law of a split algebra on arbitrary commutative test algebras. -/

noncomputable section

namespace Langlands.ReducedNorm

universe uK uA uI uR uS

open scoped TensorProduct

variable {K : Type uK} [Field K] {A : Type uA} [Ring A] [Algebra K A]
  {I : Type uI} [Fintype I] [DecidableEq I]

/-- Extend a matrix chart to a commutative test algebra, by the tensor universal property. -/
def tensorChart (e : A ≃ₐ[K] Matrix I I K) (R : Type uR) [CommRing R] [Algebra K R] :
    R ⊗[K] A →ₐ[R] Matrix I I R :=
  AlgHom.liftEquiv K R A (Matrix I I R)
    (((Algebra.ofId K R).mapMatrix).comp e.toAlgHom)

@[simp] theorem tensorChart_tmul (e : A ≃ₐ[K] Matrix I I K)
    (R : Type uR) [CommRing R] [Algebra K R] (r : R) (a : A) :
    tensorChart e R (r ⊗ₜ[K] a) = r • (e a).map (algebraMap K R) := rfl

/-- Extension of a chart commutes with every coefficient-algebra map. -/
theorem tensorChart_naturality (e : A ≃ₐ[K] Matrix I I K)
    {R : Type uR} [CommRing R] [Algebra K R]
    {S : Type uS} [CommRing S] [Algebra K S] (f : R →ₐ[K] S) (x : R ⊗[K] A) :
    tensorChart e S (Algebra.TensorProduct.map f (AlgHom.id K A) x) =
      (tensorChart e R x).map f := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, tensorChart_tmul]
      ext i j
      change f r * algebraMap K S (e a i j) = f (r * algebraMap K R (e a i j))
      rw [map_mul, f.commutes]
  | add x y hx hy =>
      simpa only [map_add, Matrix.map_add f (map_add f)] using congrArg₂ (· + ·) hx hy

variable [Nonempty I]

/-- The actual determinant homomorphism on the scalar extension of a split algebra. -/
def splitNorm (e : A ≃ₐ[K] Matrix I I K)
    (R : Type uR) [CommRing R] [Algebra K R] : R ⊗[K] A →*₀ R where
  toFun x := (tensorChart e R x).det
  map_zero' := by simp
  map_one' := by simp
  map_mul' x y := by simp [Matrix.det_mul]

@[simp] theorem splitNorm_apply (e : A ≃ₐ[K] Matrix I I K)
    (R : Type uR) [CommRing R] [Algebra K R] (x : R ⊗[K] A) :
    splitNorm e R x = (tensorChart e R x).det := rfl

/-- The determinant law is natural even for noninjective maps and nonreduced algebras. -/
theorem splitNorm_naturality (e : A ≃ₐ[K] Matrix I I K)
    {R : Type uR} [CommRing R] [Algebra K R]
    {S : Type uS} [CommRing S] [Algebra K S] (f : R →ₐ[K] S) (x : R ⊗[K] A) :
    splitNorm e S (Algebra.TensorProduct.map f (AlgHom.id K A) x) =
      f (splitNorm e R x) := by
  simp only [splitNorm_apply, tensorChart_naturality]
  exact (f.map_det _).symm

/-- Scalars have norm their power by the matrix size. -/
theorem splitNorm_scalar (e : A ≃ₐ[K] Matrix I I K)
    (R : Type uR) [CommRing R] [Algebra K R] (r : R) :
    splitNorm e R (r ⊗ₜ[K] (1 : A)) = r ^ Fintype.card I := by
  simp

omit [Nonempty I] in
/-- Two field-linear matrix charts give conjugate matrices on every test algebra. -/
theorem tensorChart_conjugate (e e' : A ≃ₐ[K] Matrix I I K)
    (R : Type uR) [CommRing R] [Algebra K R] :
    ∃ V : (Matrix I I R)ˣ, ∀ x : R ⊗[K] A,
      tensorChart e' R x = (V : Matrix I I R) * tensorChart e R x *
        ((V⁻¹ : (Matrix I I R)ˣ) : Matrix I I R) := by
  obtain ⟨U, hU⟩ := MatrixAlgebra.exists_unit_conj_of_charts e e'
  let V : (Matrix I I R)ˣ := Units.map ((Algebra.ofId K R).mapMatrix).toMonoidHom U
  refine ⟨V, fun x => ?_⟩
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
      simp only [tensorChart_tmul, hU a, Matrix.map_mul]
      change r • ((U.val.map (algebraMap K R) * (e a).map (algebraMap K R)) *
        (↑U⁻¹ : Matrix I I K).map (algebraMap K R)) = _
      simp only [smul_mul_assoc, mul_smul_comm]
      rfl
  | add x y hx hy => simp only [map_add, hx, hy, mul_add, add_mul]

/-- The all-test determinant law is independent of the matrix chart. -/
theorem splitNorm_chart_independent (e e' : A ≃ₐ[K] Matrix I I K)
    (R : Type uR) [CommRing R] [Algebra K R] (x : R ⊗[K] A) :
    splitNorm e' R x = splitNorm e R x := by
  obtain ⟨V, hV⟩ := tensorChart_conjugate e e' R
  simp only [splitNorm_apply, hV x, Matrix.det_mul]
  rw [mul_right_comm, ← Matrix.det_mul]
  simp

/-- The induced norm on actual units. -/
def splitNormUnits (e : A ≃ₐ[K] Matrix I I K)
    (R : Type uR) [CommRing R] [Algebra K R] : (R ⊗[K] A)ˣ →* Rˣ :=
  Units.map (splitNorm e R).toMonoidHom

/-- The actual norm-one subgroup of units. -/
def splitNormOne (e : A ≃ₐ[K] Matrix I I K)
    (R : Type uR) [CommRing R] [Algebra K R] : Subgroup (R ⊗[K] A)ˣ :=
  (splitNormUnits e R).ker

@[simp] theorem mem_splitNormOne (e : A ≃ₐ[K] Matrix I I K)
    (R : Type uR) [CommRing R] [Algebra K R] (x : (R ⊗[K] A)ˣ) :
    x ∈ splitNormOne e R ↔ splitNorm e R (x : R ⊗[K] A) = 1 := by
  change splitNormUnits e R x = 1 ↔ _
  exact Units.ext_iff

/-- Naturality of the group homomorphism on units. -/
theorem splitNormUnits_naturality (e : A ≃ₐ[K] Matrix I I K)
    {R : Type uR} [CommRing R] [Algebra K R]
    {S : Type uS} [CommRing S] [Algebra K S] (f : R →ₐ[K] S) (x : (R ⊗[K] A)ˣ) :
    splitNormUnits e S (Units.map
        (Algebra.TensorProduct.map f (AlgHom.id K A)).toMonoidHom x) =
      Units.map f.toMonoidHom (splitNormUnits e R x) := by
  apply Units.ext
  exact splitNorm_naturality e f (x : R ⊗[K] A)

end Langlands.ReducedNorm
