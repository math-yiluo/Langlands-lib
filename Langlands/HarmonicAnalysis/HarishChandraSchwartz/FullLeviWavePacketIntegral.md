# Change of variables in the actual group-Levi wave packet

The full-root case of the wave packet in Waldspurger VI.3, printed p. 302
(PDF p. 68), supplies the group-Levi integral in the lower inclusion of
VIII.4.2, printed p. 330 (PDF p. 96). This derived comparison identifies
that integral with the ambient packet used for central Fourier inversion.

`rationalFullLeviInducingOrbitHomeomorph` reads the full-Levi orbit
homeomorphism with target the orbit of the pulled-back inducing
representative. Composing the Levi section coefficient with this
homeomorphism gives the coefficient of the chosen ambient tensor at each
point. Continuity of the Levi section coefficient at a fixed group
element follows from the smooth section in the actual Laurent coordinates.
The composition identity gives continuity of the chosen ambient tensor's
coefficient at that element.

The pushforward of the ambient normalized orbit measure is the literal
standard Levi orbit measure for the transported quotient Haar measure. The
Bochner change of variables along the orbit homeomorphism preserves the
restriction-kernel and self-twist factors in the source normalization. For
weight one, the composition identity therefore gives equality with
`rationalOrbitWavePacket` at every group point.

`standardLeviPlancherelWavePacket_fullLevi_eq_ambient` applies the published
full-root density computation to the canonical weight of the actual
standard Levi packet. The continuation, domain, irreducibility and unitary
regularity data in the standard packet appear in this comparison. Since the
full-root weight is one, the same integral equality holds for the actual
Plancherel packet. The representation carrier remains in `uV`.
