import Langlands.Geometry.Building.ChapterSevenBuildingAxiomsStatement
import Langlands.Geometry.Building.RootValuationBuildingConstructionReduction
import Langlands.Geometry.Building.ActualApartmentSplittingProof
import Langlands.Geometry.Building.AffineIwahoriTitsProof
import Langlands.Geometry.Building.AffineIwahoriTitsBuildingProof

/-! # The Chapter 7 building of supplied valuation data satisfies the Section 4.2 axioms: proof -/

universe u

namespace Langlands.Geometry.Building

/-- **The Chapter 7 building satisfies the Section 4.2 axioms** (KP Chapter 7, 4.1.28 and
Remark 7.6.5). For parahoric building data over a nonarchimedean local field satisfying V 7
and AS 2–AS 5, the quotient carries a polysimplicial realization and an apartment splitting
for which KP Axioms 4.1.1, 4.1.2, 4.1.4, AS 1, AS 6 and 4.1.9 hold. -/
theorem chapterSevenBuildingAxioms : ChapterSevenBuildingAxiomsStatement.{u} := by
  intro F _ _ _ _ G _ P hD
  obtain ⟨R, T, hR, hB, hT, hRR, _, hF, hTS⟩ :=
    P.fiveAxioms_of_statements hD (actualApartmentSplitting F G P.toValuationBuildingData hD)
      affineIwahoriTits affineIwahoriTitsBuilding
  exact ⟨R, T, hR, hB, hT, hRR, hF, hTS⟩

end Langlands.Geometry.Building
