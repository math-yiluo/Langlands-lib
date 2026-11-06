import Langlands.GroupScheme.MatrixRepresentation.AffineCoefficients
import Langlands.GroupScheme.MatrixRepresentation.FrobeniusPower
import Langlands.GroupScheme.Rational.CoordinateSemigroupReduction

/-! # Actual augmentation quotient tests and Frobenius -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation.AugmentationQuotients

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

/-- The actual coordinate algebra modulo a power of the identity ideal. -/
def quotientAlgebra (N : ℕ) : CommAlgCat.{u} (CommRingCat.of k) :=
  CommAlgCat.of (CommRingCat.of k)
    ((CharacterUnits.Coord G) ⧸ (CoordinateWeights.augmentationIdeal G) ^ N)

/-- The canonical algebra map to the augmentation quotient. -/
def quotientMap (N : ℕ) : CharacterUnits.Coord G →ₐ[CommRingCat.of k] quotientAlgebra G N :=
  Ideal.Quotient.mkₐ (CommRingCat.of k) ((CoordinateWeights.augmentationIdeal G) ^ N)

/-- The genuine affine test point represented by the quotient map. -/
def quotientPoint (N : ℕ) : G.affinePoints (quotientAlgebra G N) :=
  (Lie.pointCoordinates G).symm (quotientMap G N)

@[simp] theorem pointCoordinates_quotientPoint (N : ℕ) :
    Lie.pointCoordinates G (quotientPoint G N) = quotientMap G N :=
  (Lie.pointCoordinates G).apply_symm_apply _

variable {G} {n : Type} [Fintype n] [DecidableEq n]
  (ρ : MatrixRepresentation G n)

/-- Evaluation at the actual quotient point is entrywise reduction of the universal matrix. -/
theorem affineMatrix_quotientPoint (N : ℕ) :
    (ρ.affineMatrix (quotientAlgebra G N) (quotientPoint G N) :
      Matrix n n (quotientAlgebra G N)) =
        ρ.universalCharacterMatrix.map (quotientMap G N) := by
  have h := AffineCoefficients.universalCharacterMatrix_map ρ
    (quotientAlgebra G N) (quotientPoint G N)
  exact h.symm.trans (congrArg
    (fun f : CharacterUnits.Coord G →ₐ[CommRingCat.of k] quotientAlgebra G N =>
      ρ.universalCharacterMatrix.map f) (pointCoordinates_quotientPoint G N))

variable (G)

/-- A sufficiently high characteristic power of a quotient coordinate is its
constant term raised to the same power. This includes the zero quotient. -/
theorem quotient_pow_origin (p : ℕ) [ExpChar k p] (N e : ℕ) (hN : N ≤ p ^ e)
    (a : CharacterUnits.Coord G) :
    (quotientMap G N a) ^ p ^ e =
      (algebraMap k (quotientAlgebra G N) (Lie.coordinateOrigin G a)) ^ p ^ e := by
  have ha : a - algebraMap k (CharacterUnits.Coord G) (Lie.coordinateOrigin G a) ∈
      CoordinateWeights.augmentationIdeal G := by
    change Lie.coordinateOrigin G
      (a - algebraMap k (CharacterUnits.Coord G) (Lie.coordinateOrigin G a)) = 0
    rw [map_sub, (Lie.coordinateOrigin G).commutes]
    exact sub_self _
  have hpow : (a - algebraMap k (CharacterUnits.Coord G) (Lie.coordinateOrigin G a)) ^
      p ^ e ∈ (CoordinateWeights.augmentationIdeal G) ^ N :=
    Ideal.pow_le_pow_right hN (Ideal.pow_mem_pow ha _)
  have hz : quotientMap G N
      ((a - algebraMap k (CharacterUnits.Coord G) (Lie.coordinateOrigin G a)) ^ p ^ e) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr hpow
  rw [map_pow, map_sub, (quotientMap G N).commutes] at hz
  apply sub_eq_zero.mp
  exact (map_sub (characteristicPowerMap k p (quotientAlgebra G N) e) _ _).symm.trans hz

variable {G}

/-- The Frobenius-powered actual representation is identity on the quotient
test whenever the quotient order is at most the characteristic power. -/
theorem frobeniusPower_affineMatrix_quotientPoint (p : ℕ) [ExpChar k p]
    (N e : ℕ) (hN : N ≤ p ^ e) :
    (ρ.frobeniusPower p e).affineMatrix (quotientAlgebra G N) (quotientPoint G N) = 1 := by
  apply Units.ext
  rw [frobeniusPower_affineMatrix]
  change ((ρ.affineMatrix (quotientAlgebra G N) (quotientPoint G N) :
    Matrix n n (quotientAlgebra G N)).map
      (characteristicPowerMap k p (quotientAlgebra G N) e)) = 1
  rw [affineMatrix_quotientPoint]
  ext i j
  change (quotientMap G N (ρ.universalCharacterMatrix i j)) ^ p ^ e = _
  rw [quotient_pow_origin G p N e hN]
  have ho := congrArg (fun M : Matrix n n k => M i j)
    (AffineCoefficients.universalCharacterMatrix_origin ρ)
  change Lie.coordinateOrigin G (ρ.universalCharacterMatrix i j) = (1 : Matrix n n k) i j at ho
  rw [ho]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.one_apply_eq, map_one, one_pow]
  · simp only [Matrix.one_apply_ne hij, map_zero,
      zero_pow (pow_ne_zero _ (expChar_ne_zero k p))]

end Langlands.GroupScheme.MatrixRepresentation.AugmentationQuotients
