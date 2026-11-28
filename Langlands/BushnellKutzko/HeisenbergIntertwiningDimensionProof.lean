import Langlands.BushnellKutzko.BetaExtensionTwist.Multiplicity
import Langlands.BushnellKutzko.HeisenbergIntertwiningDimensionStatement
import Langlands.BushnellKutzko.SimpleStratumLatticePropertiesProof
import Langlands.BushnellKutzko.SimpleStratumGroupPropertiesProof
import Langlands.BushnellKutzko.HeisenbergRepresentationReduction
import Langlands.BushnellKutzko.SimpleCharacterPairingProof
import Langlands.BushnellKutzko.SimpleCharacterIntertwiningProof

/-! # Dimension of the Heisenberg intertwining space -/

open ValuativeRel
open scoped Classical Pointwise

namespace Langlands.BushnellKutzko

universe uF uV uW

/-- The Heisenberg support identifies the zero-dimensional cases, and the
index comparison gives dimension one on that support. -/
theorem heisenbergIntertwiningDimension_of_stratum_properties
    (heisenberg : HeisenbergRepresentationStatement.{uF, uV, uW, uW, uW})
    (groups : SimpleStratumGroupPropertiesStatement.{uF, uV}) :
    HeisenbergIntertwiningDimensionStatement.{uF, uV, uW} := by
  intro F _ _ _ _ V _ _ ψ hψ S hr hs q θ hθ W _ _ η hη y
  have hsupport := ((heisenberg F V ψ hψ S hr hs q θ hθ).2.2 W η hη).2.2
  dsimp only
  split
  · rename_i hy
    exact heisenberg_intertwining_finrank_eq_one heisenberg simpleStratumLatticeProperties groups
      ψ hψ S hr hs q θ hθ η hη y (hsupport ▸ hy)
  · rename_i hy
    have hz (f : intertwiningSpace η η y) : f = 0 := by
      by_contra hne
      exact hy (hsupport ▸ (show y ∈ representationSelfIntertwining η from ⟨f, hne⟩))
    let _ : Subsingleton (intertwiningSpace η η y) :=
      ⟨fun f g => (hz f).trans (hz g).symm⟩
    exact Module.finrank_zero_of_subsingleton

/-- With the stratum group properties supplied, the Heisenberg representation
theorem alone gives the dimension formula. -/
theorem heisenbergIntertwiningDimension_of_heisenberg
    (heisenberg : HeisenbergRepresentationStatement.{uF, uV, uW, uW, uW}) :
    HeisenbergIntertwiningDimensionStatement.{uF, uV, uW} :=
  heisenbergIntertwiningDimension_of_stratum_properties heisenberg simpleStratumGroupProperties

/-- The commutator pairing and the intertwining of simple characters give the
dimension formula through the reduction of the Heisenberg representation theorem. -/
theorem heisenbergIntertwiningDimension_of_pairing_intertwining
    (pairing : SimpleCharacterPairingStatement.{uF, uV})
    (intertwining : SimpleCharacterIntertwiningStatement.{uF, uV}) :
    HeisenbergIntertwiningDimensionStatement.{uF, uV, uW} :=
  heisenbergIntertwiningDimension_of_heisenberg
    (heisenbergRepresentation_of pairing intertwining simpleStratumGroupProperties)

/-- The dimension of the Heisenberg intertwining space in BK93 (5.1.8). -/
theorem heisenbergIntertwiningDimension : HeisenbergIntertwiningDimensionStatement.{uF, uV, uW} :=
  heisenbergIntertwiningDimension_of_pairing_intertwining
    simpleCharacterPairing simpleCharacterIntertwining

end Langlands.BushnellKutzko
