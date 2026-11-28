import Langlands.BushnellKutzko.BetaExtensionTwist.Reduction
import Langlands.BushnellKutzko.HeisenbergRepresentationReduction
import Langlands.BushnellKutzko.SimpleCharacterIntertwiningProof
import Langlands.BushnellKutzko.SimpleCharacterPairingProof
import Langlands.BushnellKutzko.SimpleStratumGroupPropertiesProof
import Langlands.BushnellKutzko.SimpleStratumLatticePropertiesProof

namespace Langlands.BushnellKutzko

universe uF uV uW uW₁ uW₂

/-- Bushnell–Kutzko (5.3.2), the intertwining and irreducibility of `κ ⊗ ξ`. -/
theorem betaExtensionTwist : BetaExtensionTwistStatement.{uF, uV, uW, uW₁, uW₂} :=
  betaExtensionTwist_of
    (heisenbergRepresentation_of simpleCharacterPairing simpleCharacterIntertwining
      simpleStratumGroupProperties)
    simpleStratumLatticeProperties simpleStratumGroupProperties

end Langlands.BushnellKutzko
