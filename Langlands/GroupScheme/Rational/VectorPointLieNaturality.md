# Naturality of the point-to-Lie comparison under weight isomorphisms

This internal deduction concerns actual affine group schemes over an arbitrary
field, with no restriction on characteristic or their common universe.
`vectorCoordinatesAlongIso` defines the pullback of finite vector coordinates
along an actual group-scheme isomorphism between two possibly different groups.
It composes the induced isomorphism on test-scheme points with the target
coordinates. Natural coordinates remain natural under this construction
(`IsNaturalVectorCoordinates.alongIso`).
`vectorPointLieEquiv_iso` proves that their point-to-Lie comparisons commute
with that isomorphism on points and its actual differential on the dual-number
identity kernels. Applying the injective target Lie-coordinate map reduces
the formula to the identical point coordinates under pullback.

`vectorPointLieEquiv_equivariantIso` allows independent coordinate systems
and dimensions on the two groups. Both coordinate systems must have the same
nonzero character weight for the same split torus, and the isomorphism must
intertwine those torus actions on every test scheme. The imported weight
coordinate pullback lemma gives another presentation of that weight on the
source. Uniqueness of its point-to-Lie comparison then reduces the result to
`vectorPointLieEquiv_iso`.

The provenance is internal: these are consequences of the imported natural
point-to-Lie comparison, its independence for a fixed nonzero weight, and
pullback of weight coordinates along an equivariant isomorphism. This module
does not assert coordinate independence without the weight hypotheses or
construct root-field coordinates, valuations or apartments.
