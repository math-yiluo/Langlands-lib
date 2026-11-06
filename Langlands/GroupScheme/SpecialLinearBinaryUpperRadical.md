# The actual geometric unipotent radical of the binary triangular group

Over every field, in every characteristic, the actual additive upper-root
inclusion into the binary upper-triangular special linear group is its
geometric unipotent radical. `geometricRadicalRepresentative` packages that
inclusion together with the proved
`LeviSubgroup.IsGeometricUnipotentRadical` property. The underlying source and
map are the actual additive group and `upperRootMap`.

The proof uses the previously established equality of the upper-root range
with the full kernel of the last diagonal character on every relative test
scheme. Every character of a unipotent group is trivial on all such tests,
by the published coefficient-representation argument. Consequently every
homomorphism from a unipotent group into the triangular group factors through
the root range on all tests. This proves greatestness even without imposing
closedness, smoothness, connectedness or normality on that homomorphism.

The same argument applies after arbitrary field extension: pull back the
diagonal character, use its all-test value formula, and use compatibility of
subgroup ranges with base change. The additive group is smooth, affine,
connected and unipotent; its algebraic-closure pullback is connected and
unipotent by the published field-extension results. Closedness and normality
of the root inclusion also persist after base change. These facts prove the
full radical predicate both over the ground field and its algebraic closure.

This is an internal consequence of the explicit binary matrix kernel
calculation and published character, vector-group and base-change results.
It does not assert that the triangular group is parabolic in the ambient
special linear group, or prove the general local Kneser–Tits theorem.
