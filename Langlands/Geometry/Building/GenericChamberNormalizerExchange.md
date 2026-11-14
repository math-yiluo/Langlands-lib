# Chamber exchange with the actual normalizer stabilizer

This internal helper defines `KPApartmentData.chamberNormalizer C` as the image
in the original rational-point group of the actual normalizer's setwise
stabilizer of `C`. It does not assert pointwise fixing by that stabilizer.

For connected reductive data over any field with maximal split torus, supplied
ordinary and extended affine-root-system properties, the actual derivative
identification, and AS4, the main theorem factors every element of the sharp
fixer of a chamber across a simple wall. The factors belong, in order, to the
reflected chamber's sharp fixer, the wall root group, and `chamberNormalizer C`.

The proof applies `GenericPointSharpExchange` at an interior point, choosing a
generic cocharacter positive on the wall derivative. The negative generated
root group lies in the reflected sharp fixer by
`negativeChamberRootGroups_le_reflection`. The positive generated group lies
in the reflected sharp fixer times the wall root group by
`positiveChamberRootGroups_subset_reflection_mul_wall`. The final normalizer
factor fixes the interior point. Since the actual normalizer preserves affine
roots, it carries the chamber to a chamber sharing that point, hence to the same
chamber. Combining these factors proves the asserted inclusion.

This is an internal consequence of the named published lemmas. It retains the
setwise stabilizer factor and supplies no full-group covering or common-apartment
theorem by itself.
