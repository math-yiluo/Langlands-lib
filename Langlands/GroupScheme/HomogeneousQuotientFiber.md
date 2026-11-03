# The subgroup as the actual identity fiber

Author: Worker 1436.

This internal construction applies over any base scheme and uses the supplied
actual quotient map and its exact right-coset relation on every relative test
scheme. It does not assume quotient representability or construct another model.

The identity coset is the image of the identity base point of the ambient group.
`subgroupToIdentityFiber` maps the source of the subgroup inclusion into the
actual pullback fiber constructed in `Dynamic.FlagQuotientFiber`. Its composite
with the fiber inclusion is the original subgroup map. If that map is monic,
the exact fiber relation proves the new map bijective on every test-scheme Hom
set: injectivity is cancellation of the monomorphism; surjectivity follows by
applying the relation to the identity and the fiber's group component. Yoneda's
criterion gives the actual relative-scheme isomorphism
`subgroupIdentityFiberIso`.

Consequently a smooth quotient map forces the subgroup to be smooth, by base
change to the identity coset and transport across that isomorphism. Separately,
closedness of a subgroup inclusion into an affine group forces affineness over
the base, by composition of affine morphisms. These results do not assert
connectedness of the subgroup. Their provenance is internal: the existing
actual pullback, the given all-test relation, Yoneda, and the standard smooth
base-change and affine-composition laws.
