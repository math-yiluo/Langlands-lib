import Langlands.Representation.Archimedean.GLKostantAll
import Langlands.Representation.Archimedean.LowerVermaCentral

/-!
# Kostant's multiplicity theorem for `𝔤𝔩_n(ℂ)`

Proof of `VermaGL.KostantMultiplicityStatement`: combine the reduction
`GLReynolds.kostantMultiplicity_of_central` with the proof
`VermaCentral.lowerVermaCentral` of `VermaGL.CentralCharacterStatement`.
-/

set_option autoImplicit false

namespace Langlands.Archimedean.VermaKostant

universe uW

/-- **Kostant's multiplicity theorem** for `𝔤𝔩_n(ℂ)`. -/
theorem lowerVermaKostant : VermaGL.KostantMultiplicityStatement.{uW} :=
  GLReynolds.kostantMultiplicity_of_central VermaCentral.lowerVermaCentral

end Langlands.Archimedean.VermaKostant
