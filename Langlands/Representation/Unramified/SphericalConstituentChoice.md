# Spherical constituents in independent carrier universes

Author: Worker 1273.

This internal construction chooses an actual spherical irreducible admissible
constituent of the existing normalized unramified principal series for a tuple
`z : Fin (r + 1) → ℂˣ`. The field universe `uF` and chosen representation-carrier
universe `uA` are independent, including `uA = 0`.

`exists_sphericalConstituentOfTuple` first applies the published
`SphericalExistence.sphericalConstituentExistence`, whose witness carrier lies
in `uF`. It then applies the published
`padicIrreducibleSmoothSmallRealization` to realize that witness in `uA`.
The actual representation equivalence transports admissibility and the existing
`IsSphericalConstituent` relation, including the nonzero compact-fixed vector
and the normalized principal-series subquotient.

`sphericalConstituentOfTuple` chooses such an object by classical choice.
Its specification theorem certifies the existing constituent relation, and
`sphericalConstituentOfTuple_hasSpectrum` places its class in the existing
spectrum relation with the unordered tuple `Eigenvalues.ofTuple z`.
No uniqueness or canonical choice of representative is asserted.

The provenance is internal: this is a carrier-universe adapter and a choice
construction from published Library theorems. It does not assert an L-factor
comparison or the full-correspondence unramified-normalization target.
