import Langlands.Galois.AbsoluteGeometricFrobeniusDensityStatement
import Langlands.Galois.FrobeniusDensity

/-! # Krull density of geometric Frobenius conjugacy classes -/

universe uE

namespace Langlands.GaloisRepresentation

/-- Away from any finite set of places, the conjugates of the images of actual
local geometric Frobenius lifts are dense in the absolute Galois group. -/
theorem absoluteGeometricFrobeniusDensity :
    AbsoluteGeometricFrobeniusDensityStatement.{uE} := by
  intro E _ _ S
  refine (dense_conjugates_globalGeometricFrobenius_degreeOne S).mono ?_
  rintro g ⟨v, hv, _, s, hs⟩
  exact ⟨v, geometricFrobeniusLift v, s, hv, geometricFrobeniusLift_spec v, hs.symm⟩

end Langlands.GaloisRepresentation
