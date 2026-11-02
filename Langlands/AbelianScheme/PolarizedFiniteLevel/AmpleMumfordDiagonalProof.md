# Ampleness from the Poincaré class at the inverse point

`ampleMumfordDiagonal` proves `AmpleMumfordDiagonalStatement` over every
specified one-point base, using the actual ample Mumford presentation.

The proof evaluates the actual normalized Mumford family at the identity
map and the inversion map. Their product is the unit point, and the
corresponding pullback of `L` factors through the one-point base, so its
class is trivial. The evaluation therefore has class
`[L]⁻¹ · [([-1])*L]⁻¹`. Multiplicativity of the Poincaré class in the
second variable makes its value at inversion the inverse of its value
at the identity map. The latter is the diagonal Poincaré bundle class.
Taking inverses identifies that class with `[L] · [([-1])*L]`.

Equality of bundle classes supplies an actual bundle isomorphism.
Inversion is its own inverse as a scheme map and hence is a closed
immersion. The published `closedImmersionPullbackAmple` makes its pullback
of `L` ample, and `ampleTensor` transports ampleness to the actual diagonal
bundle along the obtained isomorphism.

This is an internal derivation from the published normalization,
Poincaré-class, and ampleness operations, using the one-point
Mumford-class comparison from `CubicBundleMumfordProof`. It establishes
ampleness on the given presentation base; it does not establish descent
of ampleness along field extension or the cubic cohomology formula.

The companion lemma `poincareDiagonal_isAmple_after_fieldExtension` unpacks
`HasFieldAmpleMumfordPresentation`, constructs the changed dual witnesses
from the supplied ones, applies the diagonal theorem over that extension,
and transports ampleness along `poincareDiagonalBaseChangeIso` to the
pullback of the fixed original diagonal bundle. It makes no claim that
ampleness is reflected back to the original field. The final helper
`Datum.cubicBundle_isAmple_of_canonicalBundle` applies
`positiveTensorPowerAmple` with exponent three to the actual bundle cube.
