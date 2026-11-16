# Smooth proper parabolic models on affine etale neighbourhoods

This internal assembly packages an actual smooth proper representation and
uses the published finite-types proposition as an explicit premise to
construct such models on affine etale neighbourhoods. It does not prove
finite-types existence or global scheme representability.

`SmoothProperModel` consists of an actual scheme over the base, a
`RepresentableBy` structure for the actual parabolic presheaf, and smoothness
and properness of the same structure map. Its `universalFamily` is an actual
relative-parabolic inclusion on that scheme with `IsUniversal` evaluation.
The latter is precisely uniqueness of parameter morphisms for all actual
parabolic subgroup functors. The imported comparison identifies this with
universality for actual relative-parabolic inclusions.

`restrictedRepresentation` identifies a model of a pulled-back group with
a representation of restriction of the original presheaf along the map of
slice categories. It uses the canonical direct/iterated ambient pullback
comparison. `baseChange` pulls back a supplied model along an arbitrary
base map, retaining both geometry certificates.

`finiteAffineParabolicModel` uses the actual finite quotient coproduct and
its proved representation under supplied uniform rational field types.
The representing scheme is the same coproduct carrying the previously
proved smooth and proper structure morphism.

`AffineEtaleModel` additionally records an affine etale base neighbourhood,
a point over the specified original point, and a smooth proper model for
the pulled-back group. Given
`RelativeParabolicEtaleLocalFiniteTypesStatement`, its existence theorem
extracts the finite family on that neighbourhood and applies the preceding
finite quotient construction. The finite index set is lifted from `Fin n`
to `ULift (Fin n)` in the base universe; existence and uniqueness of the
field type are transported along the lift. `affineEtaleModel` chooses this data.
`affineEtaleModelCover` forms the actual etale cover indexed by all base
points: its jointly-surjective property follows from the recorded point
over each base point. No quasi-compactness or nonempty-base assumption is
used.

The finite-types statement remains an explicit input throughout the local
neighbourhood construction. All derivations are internal compositions of
the imported actual-family, base-change and finite quotient results; no new
literature translation is claimed.
