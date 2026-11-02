import Langlands.AlgebraicGeometry.Modules.ProperAmplePairSerreVanishingStatement
import Langlands.AlgebraicGeometry.Modules.SerreVanishing.Killing
import Langlands.AlgebraicGeometry.Modules.SerreVanishing.Adapter
import Langlands.AlgebraicGeometry.Modules.SerreVanishing.Assembly

/-! # Serre vanishing for two ample line bundles on a proper scheme over a field: proof -/

universe u

namespace Langlands.AlgebraicGeometry.Modules

/-- Serre vanishing for two ample line bundles on a proper scheme over a field. -/
theorem properAmplePairSerreVanishing : ProperAmplePairSerreVanishingStatement.{u} :=
  properAmplePairSerreVanishing_of_sectionKilling
    (SerreVanishing.sectionKilling_of_twistKilling SerreVanishing.twistKilling)

end Langlands.AlgebraicGeometry.Modules
