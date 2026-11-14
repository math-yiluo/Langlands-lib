# Actual root lines and full split data over a local ring

This is a derived helper for the split conclusion of
`HenselianFiniteResidueQuasiSplitStatement`. It assumes an arbitrary local
commutative ring, a reductive group over its spectrum and a coordinate split
torus that is maximal on every residue-field fibre. It does not construct the
torus or any extension of the base ring.

`localSplitRootSpace` assumes a supplied full coordinate root datum that is the
actual datum on every field-valued fibre. For each of its roots, it proves that
the actual exponent weight space in the Lie module is linearly isomorphic to
the base ring. The argument uses the published finite and projective actual
exponent summands. Each summand is flat and hence free over the local base.
Its scalar extension to the residue field is the corresponding actual exponent
summand by `splitTorus.exponentWeightBaseChangeEquiv`. Fibrewise maximality gives
a maximal split torus over the residue field, and the supplied datum identifies
the chosen exponent with an actual root there. The published `splitRootLieLine`
and exponent-character comparison make that extended summand one-dimensional.
Invariance of the rank of a free module under scalar extension gives rank one
over the local ring, and hence the required linear isomorphism.

`localSplitRootSpaceEquiv` chooses one such linear isomorphism for each actual
root exponent space under the same assumptions. This noncomputable definition
provides a trivialization; it claims no canonical choice or compatibility
between the choices for distinct roots.

`localSplitDataOfFibrewiseMaximalTorus` additionally assumes that the given torus
map is a closed subgroup. It uses the published
`localSplitFibrewiseRootDatumExistence` to obtain a single finite reduced full
root datum, then applies `localSplitRootSpace` to every root. Its conclusion
retains the actual supplied torus map and the full fibrewise datum, including
both coordinate lattices and the actual root-space isomorphisms.

The provenance is derived from the named Library results and Mathlib's
`Module.free_of_flat_of_isLocalRing`, scalar-extension rank equality and
classification of rank-one free modules. This module claims no independent
construction of root data, field root lines or finite etale neighborhoods.
