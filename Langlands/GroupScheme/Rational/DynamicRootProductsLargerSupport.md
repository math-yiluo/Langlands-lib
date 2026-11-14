# Dynamic root products indexed by a larger root support

This internal construction combines the published dynamic semigroup
realization, arbitrary-field unipotent ordered products, root-ray partition
lemmas, restriction to a smaller occurring support, and cyclic root comparison.

`DynamicRootProductData` records actual smooth closed representatives of a
dynamic unipotent group and of finitely many full positive-multiple relative
root groups. Its product isomorphism is an isomorphism of schemes over the
field, and its composite with the dynamic inclusion is the actual ordered
multiplication of the specified root inclusions.

`dynamicRootProductOfLargerSupport` constructs this data for a smooth affine
field group acted on by a split torus. Its roots need only lie in the roots
of another affine group with the same torus. The finite ray list enumerates
the indivisible positive roots of that larger root set. Disjointness of those
positive integral rays is explicit. The larger group need not be smooth or
reductive, and the target need not be connected or reductive.

The construction realizes the actual positive semigroup in the target,
whose resulting group is smooth, connected, affine and unipotent. Its action
weight support is the target's positive root set, hence a subset of the
larger positive root set. The source root-ray blocks partition that larger
set and satisfy the exact cross-exclusion hypothesis. The published
`HasOrderedSemigroupProducts.for_larger_support` therefore gives ordered
products using the unchanged larger blocks.

Each larger block generates its full positive cyclic semigroup. The
equivariant semigroup transport and cyclic-root comparison identify the
resulting ambient factor with the full relative root subgroup at that
character. This remains valid if the initial character is absent in the
target, if only a higher multiple occurs, or if no target weight occurs on
the ray. No extra copy of a surviving higher-root factor is inserted.
The ordered-product isomorphism then supplies the recorded scheme
isomorphism onto the actual dynamic unipotent representative.

This construction supplies compatible ray indexing for a later comparison
of product charts. It alone asserts neither compatibility under an ambient
homomorphism nor smoothness of its full kernel.
