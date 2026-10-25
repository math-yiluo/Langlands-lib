import Langlands.AlgebraicGeometry.Modules.SectionResidueStalkProof
import Langlands.AlgebraicGeometry.Modules.LineBundleFrameOpen

universe u

namespace Langlands.SchemeModule

/-- The whole residue nonvanishing locus of a line-bundle section is its trivialization open. -/
theorem lineBundleResidueOpenComparison : LineBundleResidueOpenComparison.{u} := by
  intro X L s
  rw [← lineBundle_stalkFrame_set_eq L s]
  ext x
  exact lineBundleResidueStalkCriterion X L s x

/-- Actual residue nonvanishing agrees with stalk frames and the full trivialization open. -/
theorem lineBundleSectionResidueComparison : LineBundleSectionResidueComparison.{u} :=
  ⟨lineBundleResidueStalkCriterion, lineBundleResidueOpenComparison⟩

end Langlands.SchemeModule
