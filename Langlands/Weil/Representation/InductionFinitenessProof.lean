import Langlands.Weil.Representation.InductionDimensionProof
import Langlands.Weil.Representation.InductionFiniteImageProof
import Langlands.Weil.Representation.InductionSemisimplicityProof
import Langlands.Weil.Representation.FiniteIndexRestrictionSemisimplicityProof

namespace Langlands.Weil

universe uG uV

/-- Finite-index induction gives the expected dimension and preserves and reflects
finite image and semisimplicity. Finite-index restriction preserves and reflects semisimplicity. -/
theorem representationInductionFiniteness :
    RepresentationInductionFiniteness.{uG, uV} := by
  intro G _ H _ V _ _ _ ρ
  have dimension := representationInductionDimension.{uG, uV} G H V ρ
  exact ⟨dimension.1, dimension.2,
    representationInductionFiniteImage.{uG, uV} G H V ρ,
    representationInductionSemisimplicity.{uG, uV} G H V ρ,
    fun σ => representationFiniteIndexRestrictionSemisimplicity.{uG, uV} G H V σ⟩

end Langlands.Weil
