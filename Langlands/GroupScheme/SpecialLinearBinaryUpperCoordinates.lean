import Langlands.GroupScheme.SpecialLinearBinaryUpper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Coordinates and geometry of the binary triangular special linear group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped Matrix

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.SpecialLinear.BinaryUpper.Coordinates

variable (R : CommRingCat.{u})

/-- The independent upper-right and last-diagonal coordinates. -/
abbrev Poly : Type u := MvPolynomial (Fin 2) R

/-- The last diagonal coordinate is inverted. -/
abbrev Coord : Type u := Localization.Away (X (1 : Fin 2) : Poly R)

/-- The actual quotient coordinate ring of the triangular subgroup. -/
abbrev QuotRing : Type u := CoordinateRing (Fin 2) R ⧸ upperIdeal R

/-- The generic determinant-one triangular matrix in the localized coordinates. -/
def generic : Matrix.SpecialLinearGroup (Fin 2) (Coord R) :=
  ⟨!![IsLocalization.Away.invSelf (X (1 : Fin 2) : Poly R),
      algebraMap (Poly R) (Coord R) (X 0);
      0, algebraMap (Poly R) (Coord R) (X 1)], by
    rw [Matrix.det_fin_two]
    change IsLocalization.Away.invSelf (X (1 : Fin 2) : Poly R) *
      algebraMap (Poly R) (Coord R) (X 1) -
      algebraMap (Poly R) (Coord R) (X 0) * 0 = 1
    rw [mul_zero, sub_zero, mul_comm]
    exact IsLocalization.Away.mul_invSelf _⟩

/-- The universal matrix over the triangular quotient algebra. -/
def quotMatrix : Matrix.SpecialLinearGroup (Fin 2) (QuotRing R) :=
  point (Ideal.Quotient.mkₐ R (upperIdeal R))

theorem quotMatrix_apply (i j : Fin 2) :
    quotMatrix R i j =
      Ideal.Quotient.mk (upperIdeal R) (quotient (Fin 2) R (X (i, j))) := rfl

theorem quotMatrix_lower : quotMatrix R 1 0 = 0 := by
  rw [quotMatrix_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

theorem quotMatrix_diagonal : quotMatrix R 1 1 * quotMatrix R 0 0 = 1 :=
  (diagonalUnit (⟨quotMatrix R, quotMatrix_lower R⟩ : subgroup (QuotRing R))).val_inv

theorem quotMatrix_last_isUnit : IsUnit (quotMatrix R 1 1) :=
  (diagonalUnit (⟨quotMatrix R, quotMatrix_lower R⟩ : subgroup (QuotRing R))).isUnit

/-- Send the two polynomial coordinates to the universal upper-right and last diagonal. -/
def polyToQuot : Poly R →ₐ[R] QuotRing R :=
  aeval ![quotMatrix R 0 1, quotMatrix R 1 1]

@[simp] theorem polyToQuot_zero : polyToQuot R (X 0) = quotMatrix R 0 1 := by
  simp [polyToQuot]

@[simp] theorem polyToQuot_one : polyToQuot R (X 1) = quotMatrix R 1 1 := by
  simp [polyToQuot]

/-- Classify the generic matrix and then descend through the lower-entry equation. -/
def toCoord : QuotRing R →ₐ[R] Coord R :=
  Ideal.Quotient.liftₐ _ (classify (R := R) (generic R)) (by
    intro a ha
    have hle : upperIdeal R ≤ RingHom.ker (classify (R := R) (generic R)) := by
      rw [upperIdeal, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, classify_entry]
      rfl
    exact hle ha)

theorem toCoord_mk (a : CoordinateRing (Fin 2) R) :
    toCoord R (Ideal.Quotient.mk (upperIdeal R) a) = classify (generic R) a := rfl

/-- Extend the two-coordinate specialization across the inverted diagonal variable. -/
def fromCoord : Coord R →ₐ[R] QuotRing R :=
  IsLocalization.Away.liftAlgHom (P := QuotRing R) (f := polyToQuot R) (X 1)
    (by simpa using quotMatrix_last_isUnit R)

theorem fromCoord_algebraMap (p : Poly R) :
    fromCoord R (algebraMap (Poly R) (Coord R) p) = polyToQuot R p :=
  IsLocalization.Away.lift_eq _ (by simpa using quotMatrix_last_isUnit R) p

theorem fromCoord_invSelf :
    fromCoord R (IsLocalization.Away.invSelf (X (1 : Fin 2) : Poly R)) =
      quotMatrix R 0 0 := by
  apply (quotMatrix_last_isUnit R).mul_left_cancel
  rw [quotMatrix_diagonal]
  have h := congrArg (fromCoord R)
    (IsLocalization.Away.mul_invSelf (S := Coord R) (X (1 : Fin 2) : Poly R))
  simpa only [map_mul, map_one, fromCoord_algebraMap, polyToQuot_one] using h

theorem fromCoord_generic (i j : Fin 2) :
    fromCoord R (generic R i j) = quotMatrix R i j := by
  fin_cases i <;> fin_cases j
  · exact fromCoord_invSelf R
  · exact (fromCoord_algebraMap R (X 0)).trans (polyToQuot_zero R)
  · change fromCoord R 0 = quotMatrix R 1 0
    rw [map_zero, quotMatrix_lower]
  · exact (fromCoord_algebraMap R (X 1)).trans (polyToQuot_one R)

theorem fromCoord_comp_toCoord :
    (fromCoord R).comp (toCoord R) = AlgHom.id R (QuotRing R) := by
  apply Ideal.Quotient.algHom_ext
  apply (homEquiv (n := Fin 2) (R := R) (S := QuotRing R)).injective
  change point (S := QuotRing R) (((fromCoord R).comp (toCoord R)).comp
      (Ideal.Quotient.mkₐ R (upperIdeal R))) =
    point (S := QuotRing R) ((AlgHom.id R (QuotRing R)).comp
      (Ideal.Quotient.mkₐ R (upperIdeal R)))
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [point_apply, point_apply]
  change fromCoord R (classify (generic R) (quotient (Fin 2) R (X (i, j)))) =
    quotMatrix R i j
  rw [classify_entry, fromCoord_generic]

theorem toCoord_comp_fromCoord :
    (toCoord R).comp (fromCoord R) = AlgHom.id R (Coord R) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (X (1 : Fin 2) : Poly R))
  apply MvPolynomial.algHom_ext
  intro i
  change toCoord R (fromCoord R (algebraMap (Poly R) (Coord R) (X i))) =
    algebraMap (Poly R) (Coord R) (X i)
  rw [fromCoord_algebraMap]
  fin_cases i
  · calc
      _ = toCoord R (quotMatrix R 0 1) := congrArg (toCoord R) (polyToQuot_zero R)
      _ = generic R 0 1 := classify_entry (generic R) 0 1
      _ = _ := rfl
  · calc
      _ = toCoord R (quotMatrix R 1 1) := congrArg (toCoord R) (polyToQuot_one R)
      _ = generic R 1 1 := classify_entry (generic R) 1 1
      _ = _ := rfl

/-- The actual triangular coordinate ring is the polynomial ring in two variables
localized at the last diagonal coordinate. -/
def quotEquiv : QuotRing R ≃ₐ[R] Coord R :=
  AlgEquiv.ofAlgHom (toCoord R) (fromCoord R) (toCoord_comp_fromCoord R)
    (fromCoord_comp_toCoord R)

/-- The triangular coordinate algebra is smooth over every commutative base ring. -/
theorem quot_smooth : Algebra.Smooth R (QuotRing R) := by
  let : Algebra.Smooth R (Poly R) := ⟨inferInstance, inferInstance⟩
  let : Algebra.Smooth (Poly R) (Coord R) :=
    Algebra.Smooth.of_isLocalization_Away (X (1 : Fin 2) : Poly R)
  let : Algebra.Smooth R (Coord R) := Algebra.Smooth.comp R (Poly R) (Coord R)
  exact Algebra.Smooth.of_equiv (quotEquiv R).symm

/-- The actual binary triangular special linear group is smooth. -/
theorem smooth_groupScheme : Smooth (groupScheme R).X.hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (QuotRing R))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap R (QuotRing R)).Smooth
  rw [RingHom.smooth_algebraMap]
  exact quot_smooth R

/-- Over a domain the triangular quotient algebra is a domain. -/
theorem quot_isDomain [IsDomain R] : IsDomain (QuotRing R) := by
  have : IsDomain (Coord R) :=
    IsLocalization.isDomain_localization
      (powers_le_nonZeroDivisors_of_noZeroDivisors (X_ne_zero (R := R) (1 : Fin 2)))
  exact Function.Injective.isDomain (quotEquiv R).toRingEquiv.toRingHom
    (quotEquiv R).injective

/-- Over a domain the underlying scheme of the triangular group is irreducible. -/
theorem irreducibleSpace_groupScheme [IsDomain R] :
    IrreducibleSpace (groupScheme R).X.left := by
  have : IsDomain (CommRingCat.of (QuotRing R)) := quot_isDomain R
  change IrreducibleSpace (Spec (CommRingCat.of (QuotRing R)))
  infer_instance

/-- Over a domain the actual triangular group has connected underlying space. -/
theorem connectedSpace_groupScheme [IsDomain R] :
    ConnectedSpace (groupScheme R).X.left := by
  let : IrreducibleSpace (groupScheme R).X.left := irreducibleSpace_groupScheme R
  infer_instance

end Langlands.GroupScheme.SpecialLinear.BinaryUpper.Coordinates
