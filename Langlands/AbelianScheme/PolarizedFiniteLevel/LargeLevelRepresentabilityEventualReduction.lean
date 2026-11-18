import Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelRepresentabilityStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.LevelBaseOpenChartGluingStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.ModuliZariskiSheafStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.EventualModuliZariskiSheafStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelChartCoverStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelQuasiProjectivityStatement

/-! # Eventual fine representability from gluing, the eventual sheaf property, charts and
quasi-projectivity -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- The sheaf property for every level `n ≥ 3` implies the eventual sheaf property. -/
theorem eventualModuliZariskiSheaf_of_moduliZariskiSheaf
    (H : ModuliZariskiSheafStatement) : EventualModuliZariskiSheafStatement :=
  fun P g d _ hd => ⟨0, fun n _ hn => H P g d n hd hn⟩

set_option linter.defProp false in
/-- Proved definition: open chart gluing, the eventual Zariski sheaf property, eventual
chart covers and eventual quasi-projectivity imply the published target
`LargeLevelRepresentabilityStatement`. -/
def largeLevelRepresentability_of_eventualSheaf
    (Hglue : LevelBaseOpenChartGluingStatement)
    (Hsheaf : EventualModuliZariskiSheafStatement)
    (Hchart : LargeLevelChartCoverStatement)
    (Hqp : LargeLevelQuasiProjectivityStatement) :
    LargeLevelRepresentabilityStatement := by
  intro P g d hg hd
  obtain ⟨N₀, h₀⟩ := Hsheaf P g d hg hd
  obtain ⟨N₁, h₁⟩ := Hchart P g d hg hd
  obtain ⟨N₂, h₂⟩ := Hqp P g d hg hd
  refine ⟨max N₀ (max N₁ N₂), fun n hN hn => ?_⟩
  have hN₀ : N₀ ≤ n := le_of_max_le_left hN
  have hN₁ : N₁ ≤ n := le_of_max_le_left (le_of_max_le_right hN)
  have hN₂ : N₂ ≤ n := le_of_max_le_right (le_of_max_le_right hN)
  obtain ⟨ι, X, a, ha, hcov⟩ := h₁ n hN₁ hn
  obtain ⟨Y, e, -, -, -, -⟩ := Hglue n _ (h₀ n hN₀ hn) ι X a ha hcov
  obtain ⟨hqc, m, i, hi, hcomp⟩ := h₂ n hN₂ hn Y ⟨e⟩
  exact ⟨Y, Y.toLocalizationSpec, hqc, ⟨m, i, hi, hcomp⟩, ⟨e⟩⟩

end Langlands.AbelianScheme.PolarizedFiniteLevel
