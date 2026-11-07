import Langlands.GroupScheme.MatrixRepresentation.FrobeniusPolynomialBox
import Langlands.GroupScheme.MatrixRepresentation.AugmentationQuotients

/-! # Exact Frobenius-origin quotient tests of actual affine groups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation.FrobeniusCoordinateModel

open Langlands.Algebra.PolynomialBoxQuotient
open FrobeniusPolynomialBox

variable {k : Type u} [Field k]
    (G : GroupScheme (Spec (.of k))) [IsAffineHom G.X.hom]
    (p : ℕ) [ExpChar k p] (r : ℕ)

/-- The Frobenius image of the actual augmentation ideal. -/
def quotientIdeal : Ideal (CharacterUnits.Coord G) :=
  (CoordinateWeights.augmentationIdeal G).map
    (characteristicPowerMap k p (CharacterUnits.Coord G) r)

/-- The actual coordinate algebra modulo its Frobenius augmentation ideal. -/
def quotientAlgebra : CommAlgCat.{u} k :=
  CommAlgCat.of k ((CharacterUnits.Coord G) ⧸ quotientIdeal G p r)

/-- The actual quotient algebra map. -/
def quotientMap : CharacterUnits.Coord G →ₐ[k] quotientAlgebra G p r :=
  Ideal.Quotient.mkₐ k (quotientIdeal G p r)

/-- The genuine affine test point classified by this quotient map. -/
def quotientPoint : G.affinePoints (quotientAlgebra G p r) :=
  (Lie.pointCoordinates G).symm (quotientMap G p r)

@[simp]
theorem pointCoordinates_quotientPoint :
    Lie.pointCoordinates G (quotientPoint G p r) = quotientMap G p r :=
  (Lie.pointCoordinates G).apply_symm_apply _

/-- In the exact quotient, every coordinate's characteristic power is its
identity value raised to that power. -/
theorem quotient_pow_origin (a : CharacterUnits.Coord G) :
    quotientMap G p r a ^ p ^ r =
      algebraMap k (quotientAlgebra G p r) (Lie.coordinateOrigin G a) ^ p ^ r := by
  have ha : a - algebraMap k (CharacterUnits.Coord G) (Lie.coordinateOrigin G a) ∈
      CoordinateWeights.augmentationIdeal G := by
    change Lie.coordinateOrigin G
      (a - algebraMap k (CharacterUnits.Coord G) (Lie.coordinateOrigin G a)) = 0
    rw [map_sub, (Lie.coordinateOrigin G).commutes]
    exact sub_self _
  have hpow :
      (a - algebraMap k (CharacterUnits.Coord G) (Lie.coordinateOrigin G a)) ^ p ^ r ∈
        quotientIdeal G p r :=
    Ideal.mem_map_of_mem (characteristicPowerMap k p (CharacterUnits.Coord G) r) ha
  have hz : quotientMap G p r
      ((a - algebraMap k (CharacterUnits.Coord G) (Lie.coordinateOrigin G a)) ^ p ^ r) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hpow
  rw [map_pow, map_sub, (quotientMap G p r).commutes] at hz
  exact sub_eq_zero.mp
    ((map_sub (characteristicPowerMap k p (quotientAlgebra G p r) r) _ _).symm.trans hz)

variable {G} {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n)

/-- Evaluation at this actual point reduces the original universal matrix. -/
theorem affineMatrix_quotientPoint :
    (ρ.affineMatrix (quotientAlgebra G p r) (quotientPoint G p r) :
      Matrix n n (quotientAlgebra G p r)) =
        ρ.universalCharacterMatrix.map (quotientMap G p r) := by
  have h := AffineCoefficients.universalCharacterMatrix_map ρ
    (quotientAlgebra G p r) (quotientPoint G p r)
  exact h.symm.trans (congrArg
    (fun f : CharacterUnits.Coord G →ₐ[CommRingCat.of k] quotientAlgebra G p r =>
      ρ.universalCharacterMatrix.map f) (pointCoordinates_quotientPoint G p r))

/-- The Frobenius-powered representation is identity at the exact quotient point. -/
theorem frobeniusPower_affineMatrix_quotientPoint :
    (ρ.frobeniusPower p r).affineMatrix (quotientAlgebra G p r) (quotientPoint G p r) = 1 := by
  apply Units.ext
  rw [frobeniusPower_affineMatrix]
  change ((ρ.affineMatrix (quotientAlgebra G p r) (quotientPoint G p r) :
    Matrix n n (quotientAlgebra G p r)).map
      (characteristicPowerMap k p (quotientAlgebra G p r) r)) = 1
  rw [affineMatrix_quotientPoint]
  ext i j
  change quotientMap G p r (ρ.universalCharacterMatrix i j) ^ p ^ r = _
  rw [quotient_pow_origin]
  have ho := congrArg (fun M : Matrix n n k => M i j)
    (AffineCoefficients.universalCharacterMatrix_origin ρ)
  change Lie.coordinateOrigin G (ρ.universalCharacterMatrix i j) = (1 : Matrix n n k) i j at ho
  rw [ho]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.one_apply_eq, map_one, one_pow]
  · simp only [Matrix.one_apply_ne hij, map_zero,
      zero_pow (pow_ne_zero _ (expChar_ne_zero k p))]

section PolynomialCoordinates

variable (G) {d : ℕ}
    (e : CharacterUnits.Coord G ≃ₐ[k] MvPolynomial (Fin d) k)
    (hε : ∀ a : CharacterUnits.Coord G, (e a).coeff 0 = Lie.coordinateOrigin G a)

include hε in
/-- A pointed polynomial coordinate equivalence identifies the actual
augmentation ideal with the polynomial origin ideal. -/
theorem map_augmentationIdeal :
    (CoordinateWeights.augmentationIdeal G).map e.toRingHom =
      RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin d) k →+* k) := by
  have h :
      CoordinateWeights.augmentationIdeal G =
        (RingHom.ker (MvPolynomial.constantCoeff :
          MvPolynomial (Fin d) k →+* k)).comap e.toRingHom := by
    ext a
    change Lie.coordinateOrigin G a = 0 ↔ (e a).coeff 0 = 0
    rw [hε a]
  rw [h, Ideal.map_comap_of_surjective e.toRingHom e.surjective]

include hε in
/-- The actual Frobenius augmentation ideal becomes exactly the characteristic box. -/
theorem map_quotientIdeal :
    (quotientIdeal G p r).map e.toRingHom =
      boxIdeal (k := k) (bound p d r) := by
  have hF :
      e.toRingHom.comp (characteristicPowerMap k p (CharacterUnits.Coord G) r) =
        (characteristicPowerMap k p (MvPolynomial (Fin d) k) r).comp e.toRingHom := by
    apply RingHom.ext
    intro a
    exact map_pow e a (p ^ r)
  rw [quotientIdeal, Ideal.map_map, hF, ← Ideal.map_map,
    map_augmentationIdeal G e hε]
  exact originFrobeniusIdeal_eq_boxIdeal p d r

/-- The exact actual-group quotient has the explicit polynomial box algebra model. -/
def polynomialModelEquiv :
    quotientAlgebra G p r ≃ₐ[k] boxAlgebra (k := k) (bound p d r) :=
  Ideal.quotientEquivAlg (quotientIdeal G p r) (boxIdeal (bound p d r)) e
    (map_quotientIdeal G p r e hε).symm

include hε in
theorem finite_quotientAlgebra : Module.Finite k (quotientAlgebra G p r) :=
  Module.Finite.equiv (polynomialModelEquiv G p r e hε).toLinearEquiv.symm

include hε in
theorem finrank_quotientAlgebra :
    Module.finrank k (quotientAlgebra G p r) = (p ^ r) ^ d := by
  rw [(polynomialModelEquiv G p r e hε).toLinearEquiv.finrank_eq,
    ← (originQuotientEquiv (k := k) p d r).toLinearEquiv.finrank_eq,
    finrank_originQuotient]

end PolynomialCoordinates

end Langlands.GroupScheme.MatrixRepresentation.FrobeniusCoordinateModel
