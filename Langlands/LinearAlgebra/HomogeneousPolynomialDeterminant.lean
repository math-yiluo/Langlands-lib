import Langlands.LinearAlgebra.HomogeneousPolynomialTransvection
import Mathlib.RingTheory.Localization.FractionRing

/-! # The determinant character of homogeneous polynomial substitution -/

noncomputable section

universe u w

namespace Langlands.LinearAlgebra.HomogeneousPolynomial

open MvPolynomial

variable {σ : Type w} {R : Type u} [CommRing R] [Fintype σ] [DecidableEq σ]

/-- The determinant of homogeneous linear substitution is a multiplicative
character of the full matrix monoid. -/
def determinantCharacter (d : ℕ) : Matrix σ σ R →* R where
  toFun M := (representation M d).det
  map_one' := by rw [representation_one, Matrix.det_one]
  map_mul' M N := by rw [representation_mul, Matrix.det_mul]

/-- The homogeneous determinant power formula over every commutative ring.
The proof establishes the universal integer polynomial identity in its fraction
field and then specializes the entries to the given matrix. -/
theorem det_representation (M : Matrix σ σ R) (d : ℕ) :
    (representation M d).det = M.det ^ exponent σ d := by
  let B := MvPolynomial (σ × σ) ℤ
  let K := FractionRing B
  let U : Matrix σ σ B := fun i j => X (i, j)
  have hU : (representation U d).det = U.det ^ exponent σ d := by
    apply IsFractionRing.injective B K
    simpa only [map_pow, RingHom.map_det, RingHom.mapMatrix_apply, representation_map] using
      det_representation_field (U.map (algebraMap B K)) d
  let f : B →+* R := eval₂Hom (Int.castRingHom R) (fun ij => M ij.1 ij.2)
  have hUM : U.map f = M := by
    ext i j
    exact eval₂Hom_X' _ _ _
  have hspec := congrArg f hU
  simpa only [map_pow, RingHom.map_det, RingHom.mapMatrix_apply,
    representation_map, hUM] using hspec

/-- The determinant character is exactly a natural power of the usual determinant. -/
theorem determinantCharacter_eq (M : Matrix σ σ R) (d : ℕ) :
    determinantCharacter d M = M.det ^ exponent σ d :=
  det_representation M d

end Langlands.LinearAlgebra.HomogeneousPolynomial
