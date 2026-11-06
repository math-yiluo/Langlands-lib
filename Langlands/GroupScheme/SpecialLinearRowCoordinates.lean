import Langlands.GroupScheme.SpecialLinear
import Langlands.GroupScheme.Reductive.HomogeneousPolynomialRepresentation
import Mathlib.RingTheory.Localization.FractionRing

/-! # Homogeneous row polynomials as actual special-linear coordinates -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.SpecialLinear

section Algebra

variable {n : Type} [Fintype n] [DecidableEq n] {R : Type u} [CommRing R]

/-- Substitute one row of the universal determinant-one matrix for polynomial variables. -/
def rowPolynomial (r : n) : MvPolynomial n R →ₐ[R] CoordinateRing n R :=
  aeval fun j => quotient n R (X (r, j))

@[simp] theorem rowPolynomial_C (r : n) (a : R) :
    rowPolynomial r (C a) = algebraMap R (CoordinateRing n R) a :=
  aeval_C _ _

@[simp] theorem rowPolynomial_X (r j : n) :
    rowPolynomial (R := R) r (X j) = quotient n R (X (r, j)) :=
  aeval_X _ _

/-- Specializing a row polynomial evaluates it at the corresponding row of the matrix. -/
theorem comp_rowPolynomial {S : Type u} [CommRing S] [Algebra R S]
    (φ : CoordinateRing n R →ₐ[R] S) (r : n) :
    φ.comp (rowPolynomial r) = aeval (fun j => point φ r j) := by
  ext j
  simp only [AlgHom.comp_apply, rowPolynomial_X, aeval_X, point_apply]

theorem classify_rowPolynomial {S : Type u} [CommRing S] [Algebra R S]
    (g : Matrix.SpecialLinearGroup n S) (r : n) (f : MvPolynomial n R) :
    classify g (rowPolynomial r f) = aeval (fun j => g r j) f := by
  have h := AlgHom.congr_fun (comp_rowPolynomial (classify (R := R) g) r) f
  simpa only [AlgHom.comp_apply, point_classify] using h

/-- Pullback of coordinate functions by right multiplication by a base-ring matrix. -/
def rightTranslation (g : Matrix.SpecialLinearGroup n R) :
    CoordinateRing n R →ₐ[R] CoordinateRing n R :=
  classify (universal n R * Matrix.SpecialLinearGroup.map
    (algebraMap R (CoordinateRing n R)) g)

/-- Right multiplication acts on row polynomials by the actual column substitution. -/
theorem rightTranslation_comp_rowPolynomial (g : Matrix.SpecialLinearGroup n R) (r : n) :
    (rightTranslation g).comp (rowPolynomial r) =
      (rowPolynomial r).comp (HomogeneousPolynomial.substitution (g : Matrix n n R)) := by
  ext j
  simp only [AlgHom.comp_apply, rowPolynomial_X, rightTranslation, classify_entry,
    HomogeneousPolynomial.substitution_X, HomogeneousPolynomial.variableImage,
    map_sum, map_mul, rowPolynomial_C]
  change ∑ l, universal n R r l * algebraMap R (CoordinateRing n R) (g l j) = _
  simp only [universal_apply]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem rightTranslation_rowPolynomial (g : Matrix.SpecialLinearGroup n R) (r : n)
    (f : MvPolynomial n R) :
    rightTranslation g (rowPolynomial r f) =
      rowPolynomial r (HomogeneousPolynomial.substitution (g : Matrix n n R) f) :=
  AlgHom.congr_fun (rightTranslation_comp_rowPolynomial g r) f

/-- The homogeneous row-polynomial map into the actual determinant-one coordinate ring. -/
def homogeneousRowMap (m : ℕ) (r : n) :
    homogeneousSubmodule n R m →ₗ[R] CoordinateRing n R :=
  (rowPolynomial r).toLinearMap.comp (homogeneousSubmodule n R m).subtype

@[simp] theorem homogeneousRowMap_apply (m : ℕ) (r : n)
    (f : homogeneousSubmodule n R m) :
    homogeneousRowMap m r f = rowPolynomial r (f : MvPolynomial n R) := rfl

/-- The homogeneous row map intertwines the full homogeneous action with right translation. -/
theorem homogeneousRowMap_intertwining (m : ℕ) (r : n)
    (g : Matrix.SpecialLinearGroup n R) (f : homogeneousSubmodule n R m) :
    homogeneousRowMap m r (HomogeneousPolynomial.specialLinearRepresentation m g f) =
      rightTranslation g (homogeneousRowMap m r f) :=
  (rightTranslation_rowPolynomial g r f).symm

end Algebra

section BinaryInjectivity

variable {R : Type u} [CommRing R] [IsDomain R]

private abbrev BinaryPolynomials := MvPolynomial (Fin 2) R
private abbrev BinaryFractions := FractionRing (BinaryPolynomials (R := R))

/-- A determinant-one matrix over the fraction field whose bottom row consists of the
two independent polynomial variables. -/
private def lowerRowTest : Matrix.SpecialLinearGroup (Fin 2) (BinaryFractions (R := R)) :=
  let x := algebraMap (BinaryPolynomials (R := R)) (BinaryFractions (R := R)) (X 0)
  let y := algebraMap (BinaryPolynomials (R := R)) (BinaryFractions (R := R)) (X 1)
  ⟨!![y⁻¹, 0; x, y], by
    have hy : y ≠ 0 := by
      intro h
      apply X_ne_zero (R := R) (1 : Fin 2)
      apply IsFractionRing.injective (BinaryPolynomials (R := R)) (BinaryFractions (R := R))
      simpa only [map_zero] using h
    simp [Matrix.det_fin_two, hy]⟩

private theorem classify_lowerRowTest_comp :
    (classify (R := R) (lowerRowTest (R := R))).comp (rowPolynomial 1) =
      IsScalarTower.toAlgHom R (BinaryPolynomials (R := R)) (BinaryFractions (R := R)) := by
  rw [comp_rowPolynomial, point_classify]
  ext i
  simp only [aeval_X]
  fin_cases i <;> rfl

/-- The entire binary polynomial ring embeds in the determinant-one coordinate ring by
the bottom-row variables. This uses an integral base, with no infinitude assumption. -/
theorem binaryRowPolynomial_injective :
    Function.Injective (rowPolynomial (n := Fin 2) (R := R) 1) := by
  intro f g h
  apply IsFractionRing.injective (BinaryPolynomials (R := R)) (BinaryFractions (R := R))
  have e := congrArg (classify (R := R) (lowerRowTest (R := R))) h
  change ((classify (lowerRowTest (R := R))).comp (rowPolynomial 1)) f =
    ((classify (lowerRowTest (R := R))).comp (rowPolynomial 1)) g at e
  rw [classify_lowerRowTest_comp] at e
  exact e

theorem binaryHomogeneousRowMap_injective (m : ℕ) :
    Function.Injective (homogeneousRowMap (n := Fin 2) (R := R) m 1) := by
  intro f g h
  exact Subtype.ext (binaryRowPolynomial_injective h)

end BinaryInjectivity

end Langlands.GroupScheme.SpecialLinear
