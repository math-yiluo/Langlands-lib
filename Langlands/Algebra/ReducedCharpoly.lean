import Langlands.Algebra.ReducedNormRegular
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-! The reduced characteristic polynomial defined by the canonical reduced norm. -/

noncomputable section

namespace Langlands.CentralSimple

open scoped TensorProduct
open Polynomial
open Langlands.ReducedNorm

universe u uL uJ

section General

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A]
  {J : Type uJ} [Fintype J] [DecidableEq J]

/-- The regular multiplication matrix of the generic scalar difference is its charmatrix. -/
theorem leftMulMatrix_generic_sub (b : Module.Basis J K A) (a : A) :
    Algebra.leftMulMatrix (b.baseChange K[X])
        ((X : K[X]) ⊗ₜ[K] (1 : A) - (1 : K[X]) ⊗ₜ[K] a) =
      (Algebra.leftMulMatrix b a).charmatrix := by
  apply Matrix.ext
  intro i j
  simp [Algebra.leftMulMatrix_eq_repr_mul, sub_mul,
    Matrix.charmatrix, Matrix.scalar, Matrix.diagonal, Algebra.smul_def,
    Finsupp.single_apply, eq_comm]

end General

variable (K A : Type u) [Field K] [Ring A] [Algebra K A]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]

/-- The canonical reduced characteristic polynomial of an original algebra element. -/
def reducedCharpoly (a : A) : K[X] :=
  reducedNorm K A K[X] ((X : K[X]) ⊗ₜ[K] (1 : A) - (1 : K[X]) ⊗ₜ[K] a)

/-- Under any matrix splitting chart this is the usual matrix characteristic polynomial. -/
theorem reducedCharpoly_map_chart {L : Type uL} [Field L] [Algebra K L]
    (e : L ⊗[K] A ≃ₐ[L]
      Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) L) (a : A) :
    (reducedCharpoly K A a).map (algebraMap K L) = (e (1 ⊗ₜ[K] a)).charpoly := by
  let f := Polynomial.mapAlgHom (Algebra.ofId K L)
  change f (reducedCharpoly K A a) = _
  rw [reducedCharpoly, ← reducedNorm_naturality K A f, reducedNorm_eq_det K A e L[X]]
  congr 1
  have he : e (1 ⊗ₜ[K] (1 : A)) = 1 := map_one e
  apply Matrix.ext
  intro i j
  simp [f, splittingMap_tmul, he, Matrix.charmatrix, Matrix.scalar, Matrix.diagonal,
    Matrix.map_one, Algebra.smul_def, Matrix.algebraMap_matrix_apply]

/-- The reduced characteristic polynomial is monic. -/
theorem reducedCharpoly_monic (a : A) : (reducedCharpoly K A a).Monic := by
  let L := finiteGaloisSplittingField K A
  apply Polynomial.monic_of_injective (FaithfulSMul.algebraMap_injective K L)
  rw [reducedCharpoly_map_chart K A (finiteGaloisSplittingChart K A)]
  exact Matrix.charpoly_monic _

/-- Its degree is the actual reduced degree of the algebra. -/
theorem reducedCharpoly_natDegree (a : A) :
    (reducedCharpoly K A a).natDegree = reducedDegree K A := by
  rw [← (reducedCharpoly_monic K A a).natDegree_map
    (algebraMap K (finiteGaloisSplittingField K A)),
    reducedCharpoly_map_chart K A (finiteGaloisSplittingChart K A)]
  simp

/-- Evaluating the polynomial gives the reduced norm of the scalar difference. -/
theorem reducedCharpoly_eval (a : A) (t : K) :
    (reducedCharpoly K A a).eval t =
      reducedNorm K A K (t ⊗ₜ[K] (1 : A) - (1 : K) ⊗ₜ[K] a) := by
  change Polynomial.aeval t (reducedCharpoly K A a) = _
  rw [reducedCharpoly, ← reducedNorm_naturality K A (Polynomial.aeval t)]
  simp

/-- The full regular characteristic polynomial is the reduced-degree power of this polynomial. -/
theorem charpoly_leftMulMatrix_eq_reducedCharpoly_pow
    {J : Type uJ} [Fintype J] [DecidableEq J] (b : Module.Basis J K A) (a : A) :
    (Algebra.leftMulMatrix b a).charpoly =
      reducedCharpoly K A a ^ reducedDegree K A := by
  rw [reducedCharpoly, ← norm_eq_reducedNorm_pow K A K[X],
    Algebra.norm_eq_matrix_det (b.baseChange K[X]), leftMulMatrix_generic_sub]
  rfl

end Langlands.CentralSimple

namespace Langlands.Polynomial

open _root_.Polynomial

/-- Positive powers can be cancelled for monic polynomials over a field. -/
theorem eq_of_monic_pow_eq {K : Type*} [Field K] {p q : _root_.Polynomial K}
    (hp : p.Monic) (hq : q.Monic) {n : ℕ} (hn : n ≠ 0) (h : p ^ n = q ^ n) :
    p = q := by
  apply Polynomial.eq_of_monic_of_associated hp hq
  apply associated_of_dvd_dvd
  · exact (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd hn).mp (dvd_of_eq h)
  · exact (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd hn).mp (dvd_of_eq h.symm)

end Langlands.Polynomial
