import Langlands.Global.AdelicRestrictionSplitCentreFiniteVolumeStatement
import Langlands.Global.AdelicFiniteVolumeProof

/-! # Finite volume of the restriction split-centre adelic quotient -/

namespace Langlands.Global.RestrictionSplitCentre

/-- The quotient `[G] = A_G G(F) \ G(𝔸_F)` has finite volume for every connected
reductive group over a number field and every split component of its Weil restriction. -/
theorem connectedReductiveQuotientFiniteVolume :
    ConnectedReductiveQuotientFiniteVolumeStatement :=
  connectedReductiveQuotientFiniteVolumeStatement_of_normOne
    AdelicGroupPoints.connectedReductiveFiniteVolume.{0}

end Langlands.Global.RestrictionSplitCentre
