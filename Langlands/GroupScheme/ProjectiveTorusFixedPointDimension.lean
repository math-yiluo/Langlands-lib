import Langlands.GroupScheme.ProjectiveTorusFixedPointDimensionStatement
import Langlands.GroupScheme.SplitTorusGenericWeights
import Langlands.GroupScheme.ProjectiveTorusFixedPointTransfer

/-! # The projective linear torus fixed-point dimension bound -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **The projective linear torus fixed-point bound** (Milne, Proposition 20.11). A nonempty
reduced finite-type scheme with an equivariant closed immersion into the projectivization of a
finite-dimensional split torus representation has at least `d + 1` distinct fixed rational
points whenever its topological Krull dimension is at least `d`. -/
theorem projectiveTorusFixedPointDimension : ProjectiveTorusFixedPointDimensionStatement.{u} := by
  intro k _ _ T hT n X _ _ _ _ a ρ φ hφc hφ d hd
  have := hT.smooth
  obtain ⟨P, m, hμ, hblock⟩ := SplitTorusGenericWeights.exists_genericWeights hT ρ
  exact ProjectiveTorusFixedPoint.exists_fixed_points_of_frame hφc hφ P m hμ hblock d hd

end Langlands.GroupScheme
