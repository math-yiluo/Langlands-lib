import Langlands.GroupScheme.SpecialLinearBinaryBigCell
import Mathlib.Algebra.MvPolynomial.Division

/-! # Regular entry coordinates in the binary special linear group -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.SpecialLinear

private theorem prime_quotient_mem_nonZeroDivisors
    {A : Type u} [CommRing A] [IsDomain A] {x f : A}
    (hx : Prime x) (hxf : ¬ x ∣ f) :
    Ideal.Quotient.mk (Ideal.span {f}) x ∈
      nonZeroDivisors (A ⧸ Ideal.span {f}) := by
  rw [mem_nonZeroDivisors_iff_left]
  intro q hq
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hfa : f ∣ x * a := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul] using hq
  obtain ⟨b, hb⟩ := hfa
  have hxb : x ∣ b := (hx.dvd_mul.mp ⟨a, hb.symm⟩).resolve_left hxf
  obtain ⟨c, rfl⟩ := hxb
  have ha : a = f * c := mul_left_cancel₀ hx.ne_zero (by
    calc
      x * a = f * (x * c) := hb
      _ = x * (f * c) := by ring)
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton.mpr ⟨c, ha⟩)

section CoordinateRing

variable (R : Type u) [CommRing R] [IsDomain R]

/-- Multiplication by any binary entry coordinate, as a linear map. -/
def binaryEntryMultiplication (i j : Fin 2) :
    CoordinateRing (Fin 2) R →ₗ[R] CoordinateRing (Fin 2) R :=
  LinearMap.mul R _ (quotient (Fin 2) R (X (i, j)))

/-- Every binary entry coordinate is a nonzerodivisor over an integral base ring. -/
theorem binaryEntry_mem_nonZeroDivisors (i j : Fin 2) :
    quotient (Fin 2) R (X (i, j)) ∈ nonZeroDivisors (CoordinateRing (Fin 2) R) := by
  apply prime_quotient_mem_nonZeroDivisors (MvPolynomial.X_prime (i := (i, j)))
  rintro ⟨q, hq⟩
  have h := congrArg (constantCoeff (σ := Fin 2 × Fin 2) (R := R)) hq
  simp [Matrix.det_fin_two, genericMatrix] at h

/-- Multiplication by an entry is injective in the actual determinant-one quotient. -/
theorem binaryEntryMultiplication_injective (i j : Fin 2) :
    Function.Injective (binaryEntryMultiplication R i j) := by
  intro a b h
  apply sub_eq_zero.mp
  apply (mem_nonZeroDivisors_iff_left.mp (binaryEntry_mem_nonZeroDivisors R i j))
  change quotient (Fin 2) R (X (i, j)) * (a - b) = 0
  rw [mul_sub, sub_eq_zero]
  exact h

end CoordinateRing

namespace BinaryUpper

variable (k : Type u) [Field k]

local instance : IsAffine (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)).X.left :=
  SpecialLinear.isAffine_groupScheme _ _

/-- The bottom-right affine coordinate is a nonzerodivisor of the entire coordinate algebra. -/
theorem lastEntryCoordinate_mem_nonZeroDivisors :
    lastEntryCoordinate k ∈
      nonZeroDivisors (AffineCoordinates.algebra
        (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k))) := by
  rw [mem_nonZeroDivisors_iff_left]
  intro a ha
  apply (coordinateAlgEquiv (Fin 2) k).symm.injective
  rw [map_zero]
  have h := congrArg (coordinateAlgEquiv (Fin 2) k).symm ha
  have he : (coordinateAlgEquiv (Fin 2) k).symm (lastEntryCoordinate k) =
      quotient (Fin 2) k (X (1, 1)) := by
    change (coordinateAlgEquiv (Fin 2) k).symm
      ((coordinateAlgEquiv (Fin 2) k) (rowPolynomial 1 (X 1))) = _
    rw [AlgEquiv.symm_apply_apply, rowPolynomial_X]
  rw [map_mul, map_zero, he] at h
  exact (mem_nonZeroDivisors_iff_left.mp (binaryEntry_mem_nonZeroDivisors k 1 1)) _ h

end BinaryUpper

end Langlands.GroupScheme.SpecialLinear
