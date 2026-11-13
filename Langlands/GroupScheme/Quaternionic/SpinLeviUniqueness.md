# Uniqueness of Levi lifts through a quaternionic spin cover

This internal module proves cancellation for a supplied quaternionic spin cover
on homomorphisms from a connected reductive group. Factor the cover through its
central isogeny to the connected isometry group, cancel the monomorphic identity
component inclusion, and apply
`IsCentralIsogeny.cancel_of_connectedReductive`.

The scalar parts of any two `IsLeviLift` pairs therefore agree. Their composites
agree on every coefficient algebra by the defining Levi action. Testing on the
affine coordinate algebra of Gm turns this into equality of morphisms, and
`isSplitTorus_gm.isConnectedReductive` permits cancellation. The norm-one parts
agree by the same cancellation when the actual reduced-norm-one source is
connected reductive. `IsLeviLift.unique` combines the two equalities.

All results apply over any field and retain the full scheme morphisms. The
provenance is internal, using the published spin-cover factorization, finite
isogeny cancellation, affine coordinate isomorphism, and split-torus reductivity.
No spin-kernel generation or norm-one simple-connectedness assertion is proved.
