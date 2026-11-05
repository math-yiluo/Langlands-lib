import Langlands.GroupScheme.LinearKernelTowerSectionStatement
import Langlands.GroupScheme.LinearKernelTowerSection
import Langlands.GroupScheme.LinearAdditiveExtensionSplittingProof

/-! # Homomorphic sections for finite character-linear kernel towers -/

universe u

namespace Langlands.GroupScheme.LinearKernelTower

/-- Every finite character-linear kernel tower over a diagonalizable group over an
algebraically closed field has a homomorphic section. -/
theorem sectionExistence : SectionExistenceStatement.{u} := by
  intro k _ _ Λ _ _
  dsimp only
  intro E q h
  exact exists_section_of_admitsTower linearAdditiveExtensionSplitting h

end Langlands.GroupScheme.LinearKernelTower
