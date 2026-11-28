import Langlands.BushnellKutzko.SimpleCharacterCommutatorProof
import Langlands.BushnellKutzko.SimpleCharacterPairingReduction
import Langlands.BushnellKutzko.SimpleStratumGroupPropertiesProof
import Langlands.BushnellKutzko.SimpleStratumLatticePropertiesProof

/-! # Nondegeneracy of the simple-character commutator pairing -/

namespace Langlands.BushnellKutzko

universe uF uV

/-- The evaluated commutator of a simple character induces a nondegenerate
alternating pairing on the quotient of its `J` group by its `H` group. -/
theorem simpleCharacterPairing : SimpleCharacterPairingStatement.{uF,uV} := by
  apply simpleCharacterPairing_of_mixedJ simpleStratumLatticeProperties
    simpleStratumGroupProperties
  intro F _ _ _ _ V _ _ ψ hψ S hS0 hS q r i k l hcrit hi hir hk hl hkl htrace θ hθ x y hx hy
  exact simpleCharacterMixedJCommutator ψ hψ S hS0 hS q hcrit hi hir hk hl hkl htrace hθ hx hy

end Langlands.BushnellKutzko
