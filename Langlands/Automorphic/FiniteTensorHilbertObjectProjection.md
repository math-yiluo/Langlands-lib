# Canonical-object spectra and full Hilbert projections

Author: Worker 2.

This internal derivation combines the published canonical-object whole-spectrum
comparison with the full-domain projection criterion, and uses the generic
compactness and dimension laws from `FiniteTensorHilbertCompactProjection`.
It asserts no new identification with original literature.

For a closed invariant subspace of a complete complex inner product space
with a norm-preserving action of the actual p-adic general linear group,
`HasFullSphericalProjectionSpectrum` requires two properties: its full spherical
fixed space is nontrivial, and its full canonical joint projection equals its
orthogonal projection onto that entire fixed space. Both maps act on every
vector of the closed invariant subspace. The scalar comparison theorem
identifies this relation with the existing whole-fixed-space scalar equations.
It retains the original mass-one spherical Haar measure, integral subgroup,
standard diagonal double cosets and normalized scalars.

Supply an actual irreducible admissible smooth object `A` and a genuine
representation equivalence from its original action onto the ambient smooth
intersection of the invariant subspace. `objectHasSpectrum_iff_fullProjection`
identifies `Unramified.HasSphericalHeckeSpectrum` for that object with the
concrete full-domain projection relation. The proof composes the existing
object/scalar comparison with the existing scalar/projection comparison.
The class comparison uses the existing isomorphism-class relation for this
same actual object. It chooses no representative of an arbitrary class.

The object's admissibility supplies finite-dimensional full fixed vectors
through the genuine smooth-model fixed-space equivalence. Consequently the
exact range of its full canonical joint projection is finite dimensional,
its dimension is bounded by the dimension of the object's original spherical
fixed space, and that full-domain projection is compact. These three results
require no spectral premise or smoothness of the whole completed action.
The norm, operators and vectors are unchanged; the supplied equivalence is
algebraic and need not be an isometry or continuous on the model.

When the object has the specified whole spectrum, equality of projections
and the existing fixed projection range law identify the exact full joint
projection range with the entire spherical fixed submodule. The original
fixed-space equivalence then gives equality of its dimension with the
dimension of the object's original spherical fixed space.

`HasHilbertFullProjectionSpectrum` applies the concrete relation to the actual
closed completed tensor slice, using its proved closedness and the original
completed global action's norm preservation at the local insertion. Its maps
are the existing full spherical and full fixed projection constructors at
these identical inputs. Field and original-factor universes are independent;
coefficients are complex and the rank is any positive natural number.
Its definition allows zero complementary tensors and requires no factor
admissibility or irreducibility. The generic comparison results apply through
the existing canonical smooth-object equivalence; constructing that canonical
irreducible admissible object retains its published nonzero-tail,
irreducibility and admissibility premises. No concrete comparison theorem
wrapper is exported here.

All results are conditional on the displayed actual objects, equivalences,
tensor presentations and invariant positive forms. No existence of those
data, nonzero eigenspace, prescribed spectral occurrence, classification,
decomposition or automorphic occurrence is asserted.
