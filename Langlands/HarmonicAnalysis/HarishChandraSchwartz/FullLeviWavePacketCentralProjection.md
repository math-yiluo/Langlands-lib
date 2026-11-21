# Prescribing the actual central projection of a group-Levi wave packet

The comparison uses Waldspurger's finite central-character fiber argument
in VIII.4.2, printed p. 330 (PDF p. 96). The chosen packet uses the actual
normalized orbit measure, and the central projection retains the mass of
`A_G(F) ∩ G¹` for the supplied central Haar measure.

`rationalFullLeviAmbientWavePacket` integrates the chosen ambient tensors
for an actual full-root section. The full-Levi integral comparison
identifies this integral with the actual standard packet whose density
is one.

Use the given unitary central character to form its actual circle
character. The trivial-twist ambient class lies in that circle
character's fiber, since the original representation acts by the given
character. Choose a product-induced preimage of the prescribed ordinary
coefficient at the base, then interpolate a smooth section whose other
tensors in the finite central fiber vanish. Continuity of the orbit
coefficient and integrability of the central translates give the
central Fourier inversion formula. Its value is the prescribed
coefficient multiplied by `rationalSplitCentralMass`.

The raw-image and same-level implications take a cuspidal Schwartz
realization of each full-root packet as input. The published central
convergence theorem at the trivial character gives integrability of the
unweighted translates of the chosen realization. Dividing that
realization by the positive central mass gives the raw image preimage.
For a bi-invariant coefficient, the existing compact averaging theorem
gives a preimage in the actual cuspidal Schwartz space at the same
compact open level. Each construction preserves the independent
representation carrier universe `uV`.
