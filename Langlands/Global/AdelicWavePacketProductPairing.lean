import Langlands.Global.AdelicPrincipalQuotientMeasure
import Langlands.Global.AdelicWavePacketProductPairingProof

/-! # Square integrability and pairing of the ambient profile lift

`wavePacketProductPairing` proves `WavePacketProductPairingStatement` by supplying the proved
canonical product law for `G(F) \ G(𝔸) ≅ A_G × [G]`, `principalQuotientProductMeasure`, to the
conditional factorization `wavePacketProductPairing_of_productMeasure`. -/

set_option autoImplicit false

namespace Langlands.Global

/-- **Pairing of the ambient profile lift.** For a nonzero smooth compactly supported ambient
coefficient, the lift `ambientProfileQuotientLift` is the pointwise product with the ambient
profile on representatives, preserves and reflects square integrability for every function on
`[G]`, and multiplies the pairing of square-integrable functions by the strictly positive square
integral of the profile on `A_G`, all for the fixed quotient measures. -/
theorem wavePacketProductPairing : WavePacketProductPairingStatement :=
  wavePacketProductPairing_of_productMeasure RestrictionSplitCentre.principalQuotientProductMeasure

end Langlands.Global
