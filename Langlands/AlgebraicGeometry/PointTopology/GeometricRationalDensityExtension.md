# Rational density after extension of the base field

Worker 1337. This internal companion to Worker 1574's
`GeometricRationalPoints` proves that `HasDenseRationalPoints k X` implies
`HasDenseGeometricRationalPoints k K X` for every extension of fields `K/k`.
There are no finite type, smoothness, reducedness or infinitude assumptions.
The hypothesis already supplies ordinary density.
`RationalDensityExtensionStatement` records this universal proposition.

For a ground-field section `p`, `isPullback_geometricRationalPoint` proves that
the section and its actual scalar extension form a Cartesian square. The
composite square across the two projections is a pullback because the structure
map composed with the section is the identity. Cancellation of the right-hand
pullback square gives the section square.

Mathlib's `Scheme.image_preimage_eq_of_isPullback` then identifies the range of
the extended section with the inverse image of the range of the original
section under `X_K → X`. Every scheme map to the spectrum of a field is
universally open, so this projection is open. The inverse image of a dense
subset under an open map is dense. Applying this to the union of the
ground-field sections and using the range identity proves the density theorem.

This is a derived categorical and topological result, using Mathlib's pullback
and universal openness theorems and the Library's actual identity-test
`RationalPoint` and ordinary density convention. It does not supply ordinary
rational density of a maximal-torus parameter scheme.
