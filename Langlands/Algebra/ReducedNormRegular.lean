import Langlands.Algebra.ReducedNorm
import Mathlib.RingTheory.Norm.Basic

/-! The regular-representation norm is the reduced norm raised to the reduced degree. -/

noncomputable section

namespace Langlands.CentralSimple

open scoped TensorProduct

universe u uR uS uI uJ

section General

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A]
  {J : Type uJ} [Fintype J] [DecidableEq J]
  {R : Type uR} [CommRing R] [Algebra K R]
  {S : Type uS} [CommRing S] [Algebra K S]

/-- Left regular matrices in a base-changed basis commute with scalar-algebra maps. -/
theorem leftMulMatrix_baseChange_map (b : Module.Basis J K A)
    (f : R →ₐ[K] S) (x : R ⊗[K] A) :
    Algebra.leftMulMatrix (b.baseChange S)
        (Algebra.TensorProduct.map f (AlgHom.id K A) x) =
      (Algebra.leftMulMatrix (b.baseChange R) x).map f := by
  classical
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    ext i j
    simp [Algebra.leftMulMatrix_eq_repr_mul, Algebra.smul_def]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    exact (Matrix.map_add f (map_add f) _ _).symm

/-- The actual regular-representation norm commutes with all maps on scalar test algebras. -/
theorem norm_baseChange_naturality (b : Module.Basis J K A)
    (f : R →ₐ[K] S) (x : R ⊗[K] A) :
    Algebra.norm S (Algebra.TensorProduct.map f (AlgHom.id K A) x) =
      f (Algebra.norm R x) := by
  classical
  rw [Algebra.norm_eq_matrix_det (b.baseChange S),
    Algebra.norm_eq_matrix_det (b.baseChange R), leftMulMatrix_baseChange_map]
  exact (RingHom.map_det f.toRingHom _).symm

/-- The norm on actual units obtained from the left regular representation. -/
def regularNormUnits (R : Type uR) [CommRing R] [Algebra K R] :
    (R ⊗[K] A)ˣ →* Rˣ :=
  Units.map (Algebra.norm R)

end General

section Matrix

variable {R : Type uR} [CommRing R]
  {I : Type uI} [Fintype I] [DecidableEq I]

/-- Left multiplication acts by the same matrix independently on every column. -/
theorem norm_matrix (a : Matrix I I R) :
    Algebra.norm R a = a.det ^ Fintype.card I := by
  let e := (Matrix.transposeLinearEquiv I I R R).trans
    (Matrix.ofLinearEquiv R).symm
  have he :
      e.toLinearMap ∘ₗ Algebra.lmul R (Matrix I I R) a ∘ₗ e.symm.toLinearMap =
        LinearMap.pi (fun i : I => (Matrix.toLin' a).comp (LinearMap.proj i)) := by
    ext m i j
    simp [e, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Matrix.toLin'_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  rw [Algebra.norm_apply, ← LinearMap.det_conj _ e, he, LinearMap.det_pi]
  simp [LinearMap.det_toLin']

end Matrix

section CentralSimple

variable (K A : Type u) [Field K] [Ring A] [Algebra K A]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]

/-- On every test algebra, the regular norm is the reduced-degree power of reduced norm. -/
theorem norm_eq_reducedNorm_pow (R : Type uR) [CommRing R] [Algebra K R]
    (x : R ⊗[K] A) :
    Algebra.norm R x = reducedNorm K A R x ^ reducedDegree K A := by
  let L := finiteGaloisSplittingField K A
  let E := L ⊗[K] R
  let f : R →ₐ[K] E := Algebra.TensorProduct.includeRight
  let e := finiteGaloisSplittingChart K A
  let y := Algebra.TensorProduct.map f (AlgHom.id K A) x
  apply Algebra.TensorProduct.includeRight_injective
    (FaithfulSMul.algebraMap_injective K L)
  change f (Algebra.norm R x) = f (reducedNorm K A R x ^ reducedDegree K A)
  rw [map_pow, ← reducedNorm_naturality K A f x,
    ← norm_baseChange_naturality (Module.finBasis K A) f x]
  change Algebra.norm E y = reducedNorm K A E y ^ reducedDegree K A
  rw [← Algebra.norm_eq_of_algEquiv (Langlands.ReducedNorm.extendSplittingChart e E) y,
    norm_matrix, Fintype.card_fin, Langlands.ReducedNorm.extendSplittingChart_apply,
    ← reducedNorm_eq_det K A e E y]

/-- The actual units homomorphism for regular norm is the same power of reduced norm on units. -/
theorem regularNormUnits_eq_pow (R : Type uR) [CommRing R] [Algebra K R] :
    regularNormUnits (K := K) (A := A) R =
      reducedNormUnits K A R ^ reducedDegree K A := by
  ext x
  exact norm_eq_reducedNorm_pow K A R (x : R ⊗[K] A)

end CentralSimple

end Langlands.CentralSimple
