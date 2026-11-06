# The simple-root quotient torus and its action

Author: Worker 1467.

This internal construction is derived from the supplied root datum and base,
the published character realization for split tori, the diagonalizable
faithful-flatness theorem, the published root-kernel centrality theorem,
and descent of automorphic actions. It introduces no external-source claim.

For an actual supplied split pinning `p`, `rootScalingTorus` is the split torus
with one coordinate for each index in the supplied simple-root support.
`rootScalingProjection` is the actual map from `p.torus` whose pullback sends
each coordinate character to the corresponding actual simple root.
The character map is injective by linear independence of the base. The
accompanying `CharacterFaithfullyFlat` helper identifies actual split-torus
maps with restriction in their canonical diagonalizable models, so injectivity
makes this projection flat and surjective. Maps of split tori over a field are
locally of finite presentation, giving an actual fppf projection.

Every root is an integral linear combination of simple roots. It therefore
factors through this projection. The published kernel centrality theorem,
using the smoothness and connectedness in the supplied reductivity data, shows
that its full scheme-theoretic kernel maps centrally into the supplied group.
Conjugation by this kernel is trivial on every test scheme. The published
fpqc descent construction then defines `rootScalingAction`, an actual action
of the simple-root torus by group automorphisms. Its restriction along the
projection is exactly conjugation by the original supplied torus.

The construction retains arbitrary fields and universe, the original full
character lattice and central torus factors, and an empty simple-root support.
No smoothness or saturation of the projection kernel is assumed. No lift of a
rational point of the quotient torus to a rational point of the supplied torus
is chosen. Compatibility with the chosen Lie root vectors, evaluation at a
tuple of scalars, and the complete pinned-isomorphism target remain additional
obligations beyond this construction.
