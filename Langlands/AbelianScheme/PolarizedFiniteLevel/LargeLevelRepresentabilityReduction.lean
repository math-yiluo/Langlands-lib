import Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelRepresentabilityStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.LevelBaseOpenChartGluingStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.ModuliZariskiSheafStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelChartCoverStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelQuasiProjectivityStatement

/-! # Eventual fine representability from gluing, the sheaf property, charts and
quasi-projectivity -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

set_option linter.defProp false in
/-- Proved definition: the four named statements imply the published target
`LargeLevelRepresentabilityStatement`. -/
def largeLevelRepresentability_of_chartCover
    (Hglue : LevelBaseOpenChartGluingStatement)
    (Hsheaf : ModuliZariskiSheafStatement)
    (Hchart : LargeLevelChartCoverStatement)
    (Hqp : LargeLevelQuasiProjectivityStatement) :
    LargeLevelRepresentabilityStatement := by
  intro P g d hg hd
  obtain ⟨N₁, h₁⟩ := Hchart P g d hg hd
  obtain ⟨N₂, h₂⟩ := Hqp P g d hg hd
  refine ⟨max N₁ N₂, fun n hN hn => ?_⟩
  obtain ⟨ι, X, a, ha, hcov⟩ := h₁ n (le_of_max_le_left hN) hn
  obtain ⟨Y, e, -, -, -, -⟩ := Hglue n _ (Hsheaf P g d n hd hn) ι X a ha hcov
  obtain ⟨hqc, m, i, hi, hcomp⟩ := h₂ n (le_of_max_le_right hN) hn Y ⟨e⟩
  exact ⟨Y, Y.toLocalizationSpec, hqc, ⟨m, i, hi, hcomp⟩, ⟨e⟩⟩

end Langlands.AbelianScheme.PolarizedFiniteLevel
