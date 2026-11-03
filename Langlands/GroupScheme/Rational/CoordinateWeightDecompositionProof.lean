import Langlands.GroupScheme.Rational.CoordinateCotangentIndependence
import Langlands.GroupScheme.Rational.CoordinateWeightPointedReduction
import Langlands.GroupScheme.Rational.PointedCoordinateDecompositionProof
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-! # Actual coordinate, augmentation and cotangent weight decompositions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.CoordinateWeights

/-- The actual coordinate algebra, augmentation ideal and cotangent of an affine
group under a split-torus action decompose into their character spaces, and the
augmentation quotient maps onto each cotangent space of the same character. -/
theorem coordinateWeightDecomposition : CoordinateWeightDecompositionStatement.{u} := by
  apply coordinateWeightDecompositionStatement_of_pointed
    PointedCoordinateWeights.pointedCoordinateDecomposition
  intro k _ G hAff S hS b
  let _ := hAff
  let _ : IsAffineHom S.X.hom := hS.isAffineHom
  refine ⟨cotangentWeightSpace_iSupIndep b, ?_⟩
  intro χ q hq
  obtain ⟨f, hf, rfl⟩ := hq
  exact cotangentMk_mem_weightSpace b χ hf

end Langlands.GroupScheme.CoordinateWeights
