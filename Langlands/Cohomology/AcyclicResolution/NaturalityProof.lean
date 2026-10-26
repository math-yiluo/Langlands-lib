import Langlands.Cohomology.AcyclicResolution.Comparison
import Langlands.Cohomology.AcyclicResolution.Statement

/-!
# Naturality of the resolution comparison

A proof of `Langlands.Cohomology.ResolutionComparisonNaturalityStatement`: maps of right
resolutions lying over `f : A ⟶ B` commute with the comparison maps to the right derived
functors. It is `Langlands.Cohomology.AcyclicResolution.comparison_naturality` after unfolding
`comparison` and reassociating. See the paired Markdown.
-/

open CategoryTheory

namespace Langlands.Cohomology

universe u v u' v'

/-- Augmentation-compatible maps between right resolutions commute with the comparison to
right-derived functors. -/
theorem resolutionComparisonNaturalityStatement :
    ResolutionComparisonNaturalityStatement.{u, v, u', v'} := by
  intro C _ _ _ D _ _ F _ A B K L ε η _ _ f g hg I J φ ψ hφ hψ n
  have h := AcyclicResolution.comparison_naturality F ε η f g hg φ ψ hφ hψ n
  rw [AcyclicResolution.comparison, AcyclicResolution.comparison, Category.assoc] at h
  exact h

end Langlands.Cohomology
