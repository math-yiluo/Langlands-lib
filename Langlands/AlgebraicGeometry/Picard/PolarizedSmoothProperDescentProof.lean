import Langlands.AlgebraicGeometry.Picard.PolarizedSmoothProperDescentStatement
import Langlands.AlgebraicGeometry.Picard.PolarizedSmoothProperDescentReduction
import Langlands.AlgebraicGeometry.Picard.PolarizedEtaleRelationEffectivityProof

/-! # Polarized smooth proper representability descends along affine étale covers: proof -/

universe u v

namespace Langlands.AlgebraicGeometry.Picard

/-- Polarized smooth proper representability descends along surjective étale maps
between affine schemes, with independent scheme and presheaf-value universes. -/
theorem polarizedSmoothProperEtaleDescent :
    PolarizedSmoothProperEtaleDescentStatement.{u, v} :=
  polarizedSmoothProperEtaleDescent_of_effectivity.{u, v}
    polarizedEtaleRelationEffectivity.{u}

end Langlands.AlgebraicGeometry.Picard
