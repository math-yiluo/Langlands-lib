# Relative tests by packets with one inducing form

`StandardParabolicFamily.IsSingleFormWavePacket` is the full-parameter packet presentation for one inducing form and one smooth compactly supported coefficient at a standard parabolic. It uses the same meromorphic continuation and agreement with the regular Eisenstein series as `IsWavePacket`.

`RelativeWavePacketSingleFormTestStatement` assumes the weighted square-integrability of full wave packets expressed by `WavePacketRapidDecayStatement`. For a logarithmically square-integrable tested form, orthogonality to the full single-form packets of the supplied standard family implies absolute convergence and zero for each single-form relative packet pairing on the norm-one quotient.

The proof presents the relative test as a packet with one summand and uses its descent to the quotient. The ambient lift multiplies by a smooth compactly supported spectral profile, using the product coefficient and concatenated coordinates for the same inducing form and continuation. Orthogonality therefore applies to this single-form lift. Fourier inversion at the unitary central character supplies a profile with nonzero centre pairing. The opposite logarithmic weights give absolute convergence of the full pairing, and the quotient product factors it into the centre pairing and the relative pairing.

This is the split-centre test used before Lemma 7.11 in Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics 426 (2023), pp. 34–35.
