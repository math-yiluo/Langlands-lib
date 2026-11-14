# Ordered dynamic root products with supplied ray geometry

This is an internal derived supporting unit. It generalizes the construction
in `DynamicRootProductAssembly` and the single-group proof in
`Reductive/SplitBigCellField` by retaining the root-ray hypotheses directly.
It does not assert that those hypotheses hold for every nonreductive group.

`orderedProductIsoOfRepresentatives` works over any base scheme. Given an
ordered-product isomorphism onto a representative of a subgroup functor, it
transports that chart to any specified representatives of the same factor
functors and image functor. It uses the actual representing isomorphisms and
the induced finite-product map. Its companion equation identifies the
transported chart's composite with the specified image inclusion as exactly
the ordered multiplication of the specified factor inclusions. The formula
also covers an empty family.

Over a field of arbitrary universe `u`,
`dynamicRootOrderedProduct_of_disjoint_positive_rays` assumes a smooth
connected affine group, a map from a split torus, a cocharacter, disjoint
positive integral rays through distinct indivisible positive actual roots,
and a finite injective enumeration of exactly those roots. It supplies
actual closed smooth connected split-unipotent representatives of the
dynamic radical and the root factors, and a scheme isomorphism from their
ordered product to that radical. The composite into the ambient group is
exactly the ordered multiplication. There is no reductivity, maximality,
or monomorphy assumption on the torus map.

The proof realizes the positive character semigroup, identifies its induced
torus-action weight support with the positive actual roots, and applies the
published ordered-semigroup-product theorem for smooth connected unipotent
groups. The positive-pairing descent in `RootRayDecomposition` gives the ray
cover without reductivity. The supplied ray disjointness gives precisely the
block disjointness and cross-exclusion needed by that theorem. Equivariant
closed-inclusion transport and cyclic root-functor comparison identify the
factors as the actual root groups. Dynamic-semigroup comparison identifies
the image as the actual dynamic radical.

`exists_dynamicRootProductIso_of_representatives` retains the same field,
group, torus, cocharacter, and ray assumptions. For any supplied
representatives of those actual root functors and of the dynamic radical,
it supplies the product isomorphism with the exact original ambient
inclusion equation, using the general representative transport.

The unit supplies a field ingredient for an integral root-product argument.
It proves neither fibrewise constancy of ray data nor an integral
root-product isomorphism, and does not establish the parahoric-model target.
