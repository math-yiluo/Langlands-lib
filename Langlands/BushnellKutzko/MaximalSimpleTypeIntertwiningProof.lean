import Langlands.BushnellKutzko.BetaExtensionTwist.Reduction
import Langlands.BushnellKutzko.HeisenbergRepresentationReduction
import Langlands.BushnellKutzko.MaximalSimpleTypeIntertwiningReduction
import Langlands.BushnellKutzko.SimpleCharacterIntertwiningProof
import Langlands.BushnellKutzko.SimpleCharacterPairingProof

/-! # Intertwining of maximal simple types -/

namespace Langlands.BushnellKutzko

universe uF uV uW

/-- The intertwining of a maximal simple type of kind (a) is `E^× J`, and
every element of `E^×` normalizes the pair. For kind (b) the intertwining is `F^× J`. -/
theorem maximalSimpleTypeIntertwining : MaximalSimpleTypeIntertwiningStatement.{uF, uV, uW} :=
  maximalSimpleTypeIntertwining_of_twist
    (betaExtensionTwist_of
      (heisenbergRepresentation_of simpleCharacterPairing simpleCharacterIntertwining
        simpleStratumGroupProperties)
      simpleStratumLatticeProperties simpleStratumGroupProperties)

end Langlands.BushnellKutzko
