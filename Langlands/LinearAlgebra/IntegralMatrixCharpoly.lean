import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.RingTheory.Polynomial.IsIntegral

/-! # Characteristic-polynomial coefficients of an integral matrix -/

noncomputable section

namespace Langlands.LinearAlgebra

open Polynomial

variable {R F n : Type*} [CommRing R] [Field F] [Algebra R F]
  [Fintype n] [DecidableEq n]

/-- Every eigenvalue in the coefficient field of an integral matrix is integral. -/
theorem isIntegral_of_isRoot_charpoly {A : Matrix n n F} (hA : IsIntegral R A)
    {x : F} (hx : A.charpoly.IsRoot x) : IsIntegral R x := by
  obtain ⟨p, hp, hpa⟩ := hA
  have hmap : aeval A (p.map (algebraMap R F)) = 0 := by
    rw [← aeval_eq_aeval_map (IsScalarTower.algebraMap_eq R F (Matrix n n F)) p A]
    exact hpa
  have hmin : (minpoly F A).IsRoot x := by
    rw [← Matrix.minpoly_toLin']
    apply Module.End.isRoot_of_hasEigenvalue
    apply (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
    simpa using hx
  refine ⟨p, hp, ?_⟩
  rw [← aeval_def, aeval_def, ← eval_map]
  exact (hmin.dvd (minpoly.dvd F A hmap)).eq_zero

/-- Integrality of a matrix as an algebra element implies integrality of every
coefficient of its characteristic polynomial, including the empty matrix. -/
theorem isIntegral_charpoly_coeff {A : Matrix n n F} (hA : IsIntegral R A) (i : ℕ) :
    IsIntegral R (A.charpoly.coeff i) := by
  let E := AlgebraicClosure F
  let f : F →ₐ[R] E := IsScalarTower.toAlgHom R F E
  let B : Matrix n n E := f.mapMatrix A
  have hB : IsIntegral R B := hA.map f.mapMatrix
  have hcoeff : IsIntegral R (B.charpoly.coeff i) :=
    Polynomial.isIntegral_coeff_of_factors B.charpoly
      (by simp [Matrix.charpoly_monic, isIntegral_one])
      (IsAlgClosed.splits _) (fun _ hx ↦ isIntegral_of_isRoot_charpoly hB hx) i
  apply (isIntegral_algHom_iff f (FaithfulSMul.algebraMap_injective F E)).mp
  simpa [B, f, Matrix.charpoly_map, ← Polynomial.coeff_map] using hcoeff

end Langlands.LinearAlgebra
