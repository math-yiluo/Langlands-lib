import Langlands.LinearAlgebra.MatrixSpectralClustering
import Langlands.LinearAlgebra.MatrixSemisimpleComplexification
import Mathlib.LinearAlgebra.Lagrange

/-! # Real polynomial interpolation on the complex spectrum -/

noncomputable section

open Matrix Polynomial Module

set_option autoImplicit false

namespace Langlands

variable {n : ℕ}

local notation "RMat" => Matrix (Fin n) (Fin n) ℝ
local notation "CMat" => Matrix (Fin n) (Fin n) ℂ

/-- The distinct complex characteristic roots of a real matrix. -/
def realMatrixSpectralRoots (A : RMat) : Finset ℂ :=
  matrixSpectralRoots (realMatrixComplexification n A)

theorem star_mem_realMatrixSpectralRoots {A : RMat} {z : ℂ}
    (hz : z ∈ realMatrixSpectralRoots A) : star z ∈ realMatrixSpectralRoots A := by
  let B := realMatrixComplexification n A
  have hpoly : B.charpoly.map (starRingEnd ℂ) = B.charpoly := by
    rw [← Matrix.charpoly_map]
    exact congrArg Matrix.charpoly (matrixEntryConjugation_complexification A)
  have hz' : B.charpoly.eval z = 0 :=
    (mem_roots B.charpoly_monic.ne_zero).mp (mem_matrixSpectralRoots.mp hz)
  have hstar := Polynomial.eval_map_apply (p := B.charpoly) (f := starRingEnd ℂ) z
  rw [hpoly, hz', map_zero] at hstar
  exact mem_matrixSpectralRoots.mpr ((mem_roots B.charpoly_monic.ne_zero).mpr hstar)

/-- Complex conjugation preserves the spectrum of a real matrix. -/
def realMatrixSpectralRootStar (A : RMat) (z : realMatrixSpectralRoots A) : realMatrixSpectralRoots A :=
  ⟨star (z : ℂ), star_mem_realMatrixSpectralRoots z.property⟩

@[simp]
theorem coe_realMatrixSpectralRootStar (A : RMat) (z : realMatrixSpectralRoots A) :
    (realMatrixSpectralRootStar A z : ℂ) = star (z : ℂ) := rfl

/-- If a matching is closer than half the separation of the base roots, it preserves conjugation. -/
theorem realMatrixSpectralMatch_star {A B : RMat} (e : realMatrixSpectralRoots A ≃ realMatrixSpectralRoots B)
    {r : ℝ} (hsep : ∀ x y : realMatrixSpectralRoots A, x ≠ y → 2 * r < dist (x : ℂ) (y : ℂ))
    (hnear : ∀ z : realMatrixSpectralRoots A, dist (e z : ℂ) (z : ℂ) < r)
    (z : realMatrixSpectralRoots A) :
    e (realMatrixSpectralRootStar A z) = realMatrixSpectralRootStar B (e z) := by
  let w := realMatrixSpectralRootStar B (e z)
  let v := e.symm w
  have hv : dist (w : ℂ) (v : ℂ) < r := by
    simpa only [v, e.apply_symm_apply] using hnear v
  have hw : dist (w : ℂ) (realMatrixSpectralRootStar A z : ℂ) < r :=
    (Complex.isometry_conj.dist_eq (e z : ℂ) (z : ℂ)).trans_lt (hnear z)
  have he : v = realMatrixSpectralRootStar A z := by
    by_contra hne
    have ht := dist_triangle_left (v : ℂ) (realMatrixSpectralRootStar A z : ℂ) (w : ℂ)
    linarith [hsep v (realMatrixSpectralRootStar A z) hne]
  rw [← he]
  exact e.apply_symm_apply w

open Classical in
/-- Interpolate prescribed complex spectral shifts at the semisimple part of a real matrix,
then take the entrywise real part. -/
def realMatrixSpectralShift (A : RMat) (d : realMatrixSpectralRoots A → ℂ) : RMat :=
  let p := Lagrange.interpolate Finset.univ (fun z : realMatrixSpectralRoots A => (z : ℂ)) d
  (aeval (realMatrixComplexification n (matrixSemisimplePart A)) p).map Complex.re

@[simp]
theorem realMatrixSpectralShift_zero (A : RMat) : realMatrixSpectralShift A 0 = 0 := by
  ext i j
  simp [realMatrixSpectralShift]

theorem continuous_realMatrixSpectralShift (A : RMat) : Continuous (realMatrixSpectralShift A) := by
  classical
  let S := realMatrixComplexification n (matrixSemisimplePart A)
  let v (z : realMatrixSpectralRoots A) : ℂ := z
  let L (d : realMatrixSpectralRoots A → ℂ) : CMat := aeval S (Lagrange.interpolate Finset.univ v d)
  have hL : L = fun d => ∑ z, d z • aeval S (Lagrange.basis Finset.univ v z) := by
    funext d
    simp only [L, Lagrange.interpolate_apply, map_sum, map_mul, aeval_C,
      Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, one_mul]
  change Continuous (fun d => (L d).map Complex.re)
  rw [hL]
  exact (continuous_finsetSum _ (fun z _ => (continuous_apply z).smul continuous_const)).matrix_map
    Complex.continuous_re

theorem realMatrixSpectralShift_mem_adjoin (A : RMat) (d : realMatrixSpectralRoots A → ℂ) :
    realMatrixSpectralShift A d ∈ Algebra.adjoin ℝ {matrixSemisimplePart A} :=
  realPart_aeval_complexification_mem_adjoin _ _

/-- For conjugation-compatible shifts, the complexified real interpolation acts by the
prescribed shift on every generalized eigenspace. -/
theorem realMatrixSpectralShift_apply (A : RMat) (d : realMatrixSpectralRoots A → ℂ)
    (hd : ∀ z, d (realMatrixSpectralRootStar A z) = star (d z))
    (z : realMatrixSpectralRoots A) (v : Fin n → ℂ)
    (hv : v ∈ Module.End.maxGenEigenspace (Matrix.toLinAlgEquiv' (realMatrixComplexification n A)) (z : ℂ)) :
    Matrix.toLinAlgEquiv' (realMatrixComplexification n (realMatrixSpectralShift A d)) v = d z • v := by
  classical
  let L : CMat ≃ₐ[ℂ] End ℂ (Fin n → ℂ) := Matrix.toLinAlgEquiv'
  let p := Lagrange.interpolate Finset.univ (fun x : realMatrixSpectralRoots A => (x : ℂ)) d
  let S := realMatrixComplexification n (matrixSemisimplePart A)
  have hEval (x : realMatrixSpectralRoots A) : p.eval (x : ℂ) = d x :=
    Lagrange.eval_interpolate_at_node d Subtype.coe_injective.injOn (Finset.mem_univ x)
  have hEvalStar : (p.map (starRingEnd ℂ)).eval (z : ℂ) = d z := by
    let w := realMatrixSpectralRootStar A z
    have h := Polynomial.eval_map_apply (p := p) (f := starRingEnd ℂ) (w : ℂ)
    rw [show (starRingEnd ℂ) (w : ℂ) = (z : ℂ) from star_star (z : ℂ), hEval w] at h
    change (p.map (starRingEnd ℂ)).eval (z : ℂ) = star (d w) at h
    rw [h, hd z, star_star]
  have hS : L S v = (z : ℂ) • v := realMatrixComplexification_semisimplePart_apply A z v hv
  have hact (q : ℂ[X]) : L (aeval S q) v = q.eval (z : ℂ) • v := by
    rw [← aeval_algHom_apply L]
    exact Module.End.aeval_apply_of_mem_apply_eq_smul hS
  change L (realMatrixComplexification n ((aeval S p).map Complex.re)) v = _
  rw [realMatrixComplexification_realPart, matrixEntryConjugation_aeval_complexification]
  change L ((1 / 2 : ℂ) • (aeval S p + aeval S (p.map (starRingEnd ℂ)))) v = _
  have hscalar : (1 / 2 : ℂ) * (d z + d z) = d z := by ring
  simp only [map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply, hact, hEval, hEvalStar,
    ← add_smul, smul_smul, hscalar]

end Langlands
