import Langlands.GroupScheme.GeneralLinear
import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section

universe u

open MvPolynomial

namespace Langlands.GroupScheme.GeneralLinear

variable (n : Type) [Fintype n] [DecidableEq n] (R : Type u) [CommRing R]

/-- Polynomial coordinates for a single matrix, before imposing invertibility. -/
abbrev MatrixPolynomial := MvPolynomial (n × n) R

/-- The matrix of the single-matrix polynomial variables. -/
def matrixVariables : Matrix n n (MatrixPolynomial n R) :=
  Matrix.of fun i j => X (i, j)

/-- The determinant of the universal polynomial matrix. -/
def determinantPolynomial : MatrixPolynomial n R := (matrixVariables n R).det

/-- The single-matrix coordinate algebra with its determinant inverted. -/
abbrev DeterminantLocalization := Localization.Away (determinantPolynomial n R)

/-- The polynomial matrix after inverting its determinant. -/
def localizedMatrix : Matrix n n (DeterminantLocalization n R) :=
  (algebraMap (MatrixPolynomial n R) (DeterminantLocalization n R)).mapMatrix
    (matrixVariables n R)

theorem localizedMatrix_det_isUnit : IsUnit (localizedMatrix n R).det := by
  rw [localizedMatrix, ← RingHom.map_det]
  exact IsLocalization.Away.algebraMap_isUnit (determinantPolynomial n R)

/-- The invertible matrix over the determinant localization. -/
def localizedUniversal : GL n (DeterminantLocalization n R) :=
  Matrix.GeneralLinearGroup.mk'' (localizedMatrix n R) (localizedMatrix_det_isUnit n R)

@[simp] theorem localizedUniversal_apply (i j : n) :
    localizedUniversal n R i j =
      algebraMap (MatrixPolynomial n R) (DeterminantLocalization n R) (X (i, j)) := rfl

/-- Classify the localized matrix by the established two-matrix coordinate quotient. -/
def toDeterminantLocalization : CoordinateRing n R →ₐ[R] DeterminantLocalization n R :=
  classify (localizedUniversal n R)

/-- Send the single-matrix polynomial variables to the original universal matrix. -/
def matrixPolynomialToCoordinate : MatrixPolynomial n R →ₐ[R] CoordinateRing n R :=
  aeval fun p => universal n R p.1 p.2

theorem matrixPolynomialToCoordinate_matrix :
    (matrixPolynomialToCoordinate n R).mapMatrix (matrixVariables n R) =
      (universal n R : Matrix n n (CoordinateRing n R)) := by
  ext i j
  simp [matrixPolynomialToCoordinate, matrixVariables]

theorem matrixPolynomialToCoordinate_det_isUnit :
    IsUnit (matrixPolynomialToCoordinate n R (determinantPolynomial n R)) := by
  rw [determinantPolynomial, AlgHom.map_det, matrixPolynomialToCoordinate_matrix]
  exact Matrix.isUnit_iff_isUnit_det _ |>.mp (universal n R).isUnit

/-- Extend the entry-coordinate map by the universal property of localization. -/
def fromDeterminantLocalization : DeterminantLocalization n R →ₐ[R] CoordinateRing n R :=
  IsLocalization.Away.liftAlgHom (determinantPolynomial n R)
    (matrixPolynomialToCoordinate_det_isUnit n R)

@[simp] theorem fromDeterminantLocalization_algebraMap (p : MatrixPolynomial n R) :
    fromDeterminantLocalization n R
      (algebraMap (MatrixPolynomial n R) (DeterminantLocalization n R) p) =
        matrixPolynomialToCoordinate n R p :=
  IsLocalization.Away.lift_eq _ (matrixPolynomialToCoordinate_det_isUnit n R) p

@[simp] theorem toDeterminantLocalization_entry (i j : n) :
    toDeterminantLocalization n R (quotient n R (X (Coordinate.entry i j))) =
      algebraMap (MatrixPolynomial n R) (DeterminantLocalization n R) (X (i, j)) := by
  exact classify_entry _ i j

@[simp] theorem fromDeterminantLocalization_entry (i j : n) :
    fromDeterminantLocalization n R
      (algebraMap (MatrixPolynomial n R) (DeterminantLocalization n R) (X (i, j))) =
        quotient n R (X (Coordinate.entry i j)) := by
  rw [fromDeterminantLocalization_algebraMap]
  simp [matrixPolynomialToCoordinate]

theorem localizedUniversal_map_from :
    Matrix.GeneralLinearGroup.map (fromDeterminantLocalization n R).toRingHom
      (localizedUniversal n R) = universal n R := by
  apply Units.ext
  ext i j
  exact fromDeterminantLocalization_entry n R i j

theorem from_comp_toDeterminantLocalization :
    (fromDeterminantLocalization n R).comp (toDeterminantLocalization n R) =
      AlgHom.id R (CoordinateRing n R) := by
  apply homEquiv.injective
  change point ((fromDeterminantLocalization n R).comp (toDeterminantLocalization n R)) =
    point (AlgHom.id R (CoordinateRing n R))
  rw [point_comp]
  change Matrix.GeneralLinearGroup.map _ (point (classify _)) = _
  rw [point_classify, point_id]
  exact localizedUniversal_map_from n R

theorem to_comp_fromDeterminantLocalization :
    (toDeterminantLocalization n R).comp (fromDeterminantLocalization n R) =
      AlgHom.id R (DeterminantLocalization n R) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (determinantPolynomial n R))
  apply MvPolynomial.algHom_ext
  intro p
  rcases p with ⟨i, j⟩
  change toDeterminantLocalization n R (fromDeterminantLocalization n R
    (algebraMap (MatrixPolynomial n R) (DeterminantLocalization n R) (X (i, j)))) = _
  rw [fromDeterminantLocalization_entry, toDeterminantLocalization_entry]
  rfl

/-- The existing GL coordinate ring is the polynomial matrix ring localized at its determinant. -/
def determinantLocalizationEquiv : CoordinateRing n R ≃ₐ[R] DeterminantLocalization n R :=
  AlgEquiv.ofAlgHom (toDeterminantLocalization n R) (fromDeterminantLocalization n R)
    (to_comp_fromDeterminantLocalization n R) (from_comp_toDeterminantLocalization n R)

@[simp] theorem determinantLocalizationEquiv_entry (i j : n) :
    determinantLocalizationEquiv n R (quotient n R (X (Coordinate.entry i j))) =
      algebraMap (MatrixPolynomial n R) (DeterminantLocalization n R) (X (i, j)) :=
  toDeterminantLocalization_entry n R i j

/-- Inverse-entry variables become the entries of the actual inverse localized matrix. -/
@[simp] theorem determinantLocalizationEquiv_inverseEntry (i j : n) :
    determinantLocalizationEquiv n R (quotient n R (X (Coordinate.inverseEntry i j))) =
      (localizedUniversal n R)⁻¹ i j :=
  classify_inverseEntry _ i j

end Langlands.GroupScheme.GeneralLinear
