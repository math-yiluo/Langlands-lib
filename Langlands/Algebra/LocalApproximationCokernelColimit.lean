import Langlands.Algebra.LocalApproximationCokernelColimitStatement
import Langlands.Algebra.LocalCompatibleMapApproximation

/-! # Colimit preservation by actual cokernels of compatible local module maps -/

namespace Langlands.Algebra

/-- The actual cokernel comparison is bijective when the source comparison is surjective
and the target comparison is bijective. -/
theorem localCokernelColimitPreservation.{uI, uA, uB, uE, uF, uR, uS, uM, uN} :
    LocalCokernelColimitPreservationStatement.{uI, uA, uB, uE, uF, uR, uS, uM, uN} := by
  intro ι _ _ _ R S _ _ _ _ _ _ D M N _ _ _ _ E F f φ hE hF
  exact φ.cokernelSystem_moduleColimitMap_bijective hE hF

end Langlands.Algebra
