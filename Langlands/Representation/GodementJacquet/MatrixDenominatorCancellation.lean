import Langlands.Representation.GodementJacquet.CentralMatrixRationality
import Langlands.Representation.GodementJacquet.GeometricDenominatorCancellation
import Langlands.Representation.RankinSelberg.RationalMonomialFunctionalEquation

/-! # Cancellation of the actual central matrix denominators -/

noncomputable section

namespace Langlands.GodementJacquet.Padic

open RankinSelberg LocalFactor

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance matrixDenominatorCancellationTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance matrixDenominatorCancellationValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance matrixDenominatorCancellationLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

variable {n : ℕ}

/-- The scalar coefficient in the shifted central geometric denominator. -/
def matrixGeometricCoefficient
    (z : Langlands.GeneralLinear (n + 1) F.Carrier) (ω : ℂ) : ℂ :=
  ω * determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) z (jpssShift n)

/-- The coefficient product of the original and reflected dual denominators
is the positive determinant norm raised to the matrix rank. -/
theorem matrixGeometricCoefficient_reflected_product
    (z : Langlands.GeneralLinear (n + 1) F.Carrier) (ω : ℂˣ) :
    matrixGeometricCoefficient F z ω *
        (matrixGeometricCoefficient F z (ω⁻¹ : ℂˣ) *
          (spectralReflectionUnit (Nat.zero_lt_one.trans
            F.canonicalTopologicalData.residueCardinality_gt_one) : ℂ) ^
              F.canonicalTopologicalData.ord (Matrix.det z.val)) =
      ((normalizedAbsoluteValue F.canonicalTopologicalData) (Matrix.det z.val) : ℂ) ^
        (n + 1) := by
  let a := (normalizedAbsoluteValue F.canonicalTopologicalData) (Matrix.det z.val)
  have ha : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    ((normalizedAbsoluteValue F.canonicalTopologicalData).pos z.det_ne_zero).ne'
  have hsp : spectralPoint F.canonicalTopologicalData.residueCardinality (1 : ℂ) =
      (F.canonicalTopologicalData.residueCardinality : ℂ)⁻¹ := by
    simp only [spectralPoint, Complex.cpow_neg_one]
  have hω : (ω : ℂ) * ((ω⁻¹ : ℂˣ) : ℂ) = 1 := by
    exact_mod_cast ω.mul_inv
  unfold matrixGeometricCoefficient
  rw [coe_spectralReflectionUnit]
  calc
    _ = determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
          z (jpssShift n) *
        (determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
          z (jpssShift n) *
            (F.canonicalTopologicalData.residueCardinality : ℂ)⁻¹ ^
              F.canonicalTopologicalData.ord (Matrix.det z.val)) := by
      calc
        _ = ((ω : ℂ) * ((ω⁻¹ : ℂˣ) : ℂ)) *
          (determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
            z (jpssShift n) *
            (determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
              z (jpssShift n) *
              (F.canonicalTopologicalData.residueCardinality : ℂ)⁻¹ ^
                F.canonicalTopologicalData.ord (Matrix.det z.val))) := by ring
        _ = _ := by rw [hω, one_mul]
    _ = determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
          z (jpssShift n) *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
          z (1 + jpssShift n) := by
      rw [determinantWeight_shift_spectral, hsp]
    _ = (a : ℂ) ^ (jpssShift n + (1 + jpssShift n)) := by
      exact (Complex.cpow_add _ _ ha).symm
    _ = (a : ℂ) ^ ((n + 1 : ℕ) : ℂ) := by
      congr 1
      simp only [jpssShift, Nat.cast_add, Nat.cast_one]
      ring
    _ = (a : ℂ) ^ (n + 1) := by rw [Complex.cpow_natCast]

/-- Determinant contraction makes the reflected coefficient product different
from one, independently of the central character. -/
theorem matrixGeometricCoefficient_reflected_product_ne_one
    (z : Langlands.GeneralLinear (n + 1) F.Carrier)
    (hz : normalizedAbsoluteValue F.canonicalTopologicalData (Matrix.det z.val) < 1)
    (ω : ℂˣ) :
    matrixGeometricCoefficient F z ω *
        (matrixGeometricCoefficient F z (ω⁻¹ : ℂˣ) *
          (spectralReflectionUnit (Nat.zero_lt_one.trans
            F.canonicalTopologicalData.residueCardinality_gt_one) : ℂ) ^
              F.canonicalTopologicalData.ord (Matrix.det z.val)) ≠ 1 := by
  rw [matrixGeometricCoefficient_reflected_product]
  have hlt := pow_lt_one₀
    ((normalizedAbsoluteValue F.canonicalTopologicalData).nonneg (Matrix.det z.val))
    hz (Nat.succ_ne_zero n)
  intro he
  have hr : normalizedAbsoluteValue F.canonicalTopologicalData (Matrix.det z.val) ^
      (n + 1) = 1 := by exact_mod_cast he
  exact (ne_of_lt hlt) hr

/-- An actual monomial functional equation and the two central geometric
clearings force the original rational function to be Laurent. -/
theorem exists_laurent_of_matrix_geometric_clearings
    (z : Langlands.GeneralLinear (n + 1) F.Carrier)
    (hz : normalizedAbsoluteValue F.canonicalTopologicalData (Matrix.det z.val) < 1)
    (ω c : ℂˣ) (m : ℤ) {R RDual : RationalFunctions}
    (hD : ∃ A : LaurentCoefficients, laurentToRatFunc A =
      laurentToRatFunc (matrixGeometricDenominator F z ω) * R)
    (hE : ∃ B : LaurentCoefficients, laurentToRatFunc B =
      laurentToRatFunc (matrixGeometricDenominator F z (ω⁻¹ : ℂˣ)) * RDual)
    (hFE : NormalizedFunctionalEquation F.canonicalTopologicalData.residueCardinality
      1 1 1 c 0 m R RDual) :
    ∃ A : LaurentCoefficients, laurentToRatFunc A = R := by
  exact exists_laurent_of_reflected_geometric_clearings
    (spectralReflectionUnit (Nat.zero_lt_one.trans
      F.canonicalTopologicalData.residueCardinality_gt_one))
    (matrixGeometricCoefficient F z ω)
    (matrixGeometricCoefficient F z (ω⁻¹ : ℂˣ))
    (F.canonicalTopologicalData.ord (Matrix.det z.val))
    (matrixGeometricCoefficient_reflected_product_ne_one F z hz ω)
    (laurentMonomialUnit c m) hD hE
    (hFE.rational_identity F.canonicalTopologicalData.residueCardinality_gt_one)

end Langlands.GodementJacquet.Padic
