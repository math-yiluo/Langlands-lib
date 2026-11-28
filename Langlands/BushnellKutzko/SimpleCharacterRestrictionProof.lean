import Langlands.BushnellKutzko.IntertwinedUnitCharacter
import Langlands.BushnellKutzko.SimpleCharacterChoiceProof
import Langlands.BushnellKutzko.SimpleCharacterIntertwiningProof
import Langlands.BushnellKutzko.SimpleCharacterRestrictionAssembly
import Langlands.BushnellKutzko.SimpleStratumGroupPropertiesProof

/-! # Restriction, twisting and nonemptiness of simple characters -/

namespace Langlands.BushnellKutzko

universe uF uV

/-- The restriction images and fibres, critical-approximation twists, and
nonemptiness of simple characters in BK93 (3.2.4)–(3.2.5), (3.3.18), and (3.3.21). -/
theorem simpleCharacterRestrictionTheorem : SimpleCharacterRestrictionStatement.{uF,uV} :=
  simpleCharacterRestriction_of_component_theorems
    intertwinedUnitCharacter simpleStratumGroupProperties
    simpleCharacterCovariance simpleCharacterChoice

end Langlands.BushnellKutzko
