# Actual coefficient action on full building facets

This module transports full apartment facets, their weak-sign closures and
chambers by the actual coefficient affine action. For supplied integer-valued
building data with torus and inclusion obtained by base change from `k`, it
transports the existing full facets and chambers of the original quotient.
The induced permutations act on its existing full facet subtype, and the unique
facet containing a point follows its coefficient transport. Hence every point
fixed by all coefficient automorphisms lies in exactly one invariant full
building facet.

The parameters are arbitrary fields `K/k` in universe `u`, an affine `k`-group
`G`, a commutative `k`-group `T`, a map with monomorphic base change, an
integer-valued valuation of `K`, a supplied KP apartment with Galois-stable
valuation class, connected reductivity of `G_K`, maximal splitness of `T_K`,
the actual centralizer data, and full V6 compatibility. `integerBuildingData`
only bundles these supplied data. It preserves the original apartment, point
carrier, quotient relation, rational-point action and facet predicate.
There is no local-field or characteristic hypothesis.

The proof uses `transportedRoots_galoisAffineAction` and generic transport in
`AffineFacetTransport`. The exact quotient semilinearity theorems
`galoisQuotientAction_smul` and `galoisQuotientAction_apartmentMap` identify
the image of every translated apartment facet with another such image.
Applying the inverse coefficient automorphism gives reflection. Taking images
of subsets defines the induced group action on facets. The unconditional
partition from `IntegerBuildingFacetPartition` identifies the full facet
containing the transported point; at a fixed point this makes its entire
facet invariant. Uniqueness follows from the same partition.

The named `GaloisFixedPointFacetStatement` is exactly the final unique invariant
facet assertion, proved by `galoisFixedPointFacet`. This is an internal deduction
from the existing definitions and the transport and partition inputs above. It does not construct a maximal invariant facet, a descended model,
a residue parabolic correspondence or an apartment containing a prescribed
fixed point. `UnramifiedFixedPointSplitTorusStatement` remains open.
