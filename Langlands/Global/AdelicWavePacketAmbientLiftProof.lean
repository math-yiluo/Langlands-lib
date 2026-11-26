import Langlands.Global.AdelicEisensteinRegularParameterProof
import Langlands.Global.AdelicWavePacketParabolicAmbientLiftProof

/-! # Lift of relative wave packets by ambient spectral coefficients

`wavePacketAmbientLift` proves `WavePacketAmbientLiftStatement` by supplying the proved
nonemptiness of regular-parameter regions, `eisensteinRegularParameter`, to the conditional
ambient lift `wavePacketAmbientLift_of_regularParameter`. -/

namespace Langlands.Global

/-- **Ambient lift of a relative wave packet.** Multiplying a relative wave packet of an actual
presented parabolic by the ambient Fourier profile `ambientWavePacketProfile eG b` of a smooth
compactly supported coefficient gives a full wave packet for the same group and compact
subgroup. -/
theorem wavePacketAmbientLift : WavePacketAmbientLiftStatement :=
  wavePacketAmbientLift_of_regularParameter eisensteinRegularParameter

end Langlands.Global
