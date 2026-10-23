import Langlands.Shimura.Coefficients.TrivializationStatement
import Langlands.Shimura.Coefficients.TorsorSectionSplittingProof
import Langlands.Shimura.Coefficients.TrivializationFromSplitting

universe u

namespace Langlands.Shimura.Coefficients

open CategoryTheory AlgebraicGeometry

/-- A finite geometric etale torsor trivializes the associated coefficient
sheaf on its localized site, naturally in the coefficient representation. -/
theorem etaleAssociatedTrivialization : EtaleAssociatedTrivializationStatement.{u} := by
  intro X G _ Y hY R _
  exact ⟨constantAssociatedTrivializationOfSplitting
    (Scheme.smallEtaleTopology X) Y (etaleTorsorSectionSplitting X G Y hY R)⟩

end Langlands.Shimura.Coefficients
