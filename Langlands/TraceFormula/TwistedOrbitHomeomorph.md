# Stabilizer cosets and locally closed twisted orbits

For a continuous automorphism `θ` of a topological group `G` and `r : G`,
`TwistedOrbit θ r` is the range of `x ↦ x⁻¹ r θ(x)` with the subspace topology.
This derived construction uses the twisted conjugation and left quotient in
`TwistedOrbital.lean`.

Equality of two orbit points is precisely the left-coset relation of the
twisted centralizer. Precomposing twisted conjugation with inversion gives a
continuous transitive left action on the orbit. In a sigma-compact locally
compact Hausdorff group, a locally closed orbit is locally compact. The open
mapping theorem for the action then makes the continuous orbit bijection
`twistedOrbitHomeomorph` a homeomorphism from the left quotient.

For a closed orbit, its inclusion in `G` is a closed embedding. The pullback
of a continuous compactly supported function along this inclusion and the
homeomorphism is continuous and compactly supported on the quotient.
`twistedOrbitFunction_integrable_of_isClosed` applies this fact to any Borel
quotient measure finite on compact sets. This is the topological and
integrability argument used for the orbital integrals in Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), pp. 487–488.
