import Langlands.Representation.Geometric.ClosedSubgroupStatement
import Langlands.Representation.Geometric.ClosedSubgroupAssembly
import Langlands.Representation.Geometric.CosetOrbitHomeomorph
import Langlands.Representation.Geometric.OrbitSectionExtensionProof

/-! The natural Mackey filtration for closed subgroups. -/

namespace Langlands.Geometric

universe uG uV

/-- The specified support filtration has the actual conjugated compact-induction
functors as its natural graded pieces. -/
theorem closedSubgroupMackeyFiltration : ClosedSubgroupMackeyFiltration.{uG, uV} := by
  intro G _ _ _ _ _ _ P Q hP hQ n s i
  exact ⟨s.supportGradedOrbitIsoOfExtension closedOrbitSectionExtension hP hQ i
    (cosetOrbitHomeomorph P Q (s.representative i) hP hQ
      (s.cosetOrbit_isLocallyClosed i))
    (cosetOrbitHomeomorph_mk P Q (s.representative i) hP hQ
      (s.cosetOrbit_isLocallyClosed i))⟩

end Langlands.Geometric
