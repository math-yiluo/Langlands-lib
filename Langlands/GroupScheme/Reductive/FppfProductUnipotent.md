# Unipotence of a supplied represented fppf product

This derived internal module proves `isUnipotent_fppfProduct` over an arbitrary
field, with the published all-test `IsUnipotent` predicate. The factors are
affine unipotent group schemes with closed inclusions into an ambient group
scheme, the first factor has normal image there, and an actual closed
representative of their fppf-local product is supplied. No smoothness,
connectedness, perfectness, or rational-point density premise is used.

The actual homomorphisms `IsFppfProduct.leftFactor` and `rightFactor` lift the
two represented factors into the supplied product. They use the published
`factorOfRangeLE` construction and the all-test containment of each factor in
the product. Their composites with the product inclusion are the original
factor inclusions. The multiplication morphism into the product is the ordered
product of these two lifted points, by cancellation of the monic product
inclusion.

`isNormal_range_of_mono_comp` reflects normality of an image through a monic
ambient inclusion on every test scheme: lift the conjugate in the ambient
image and cancel that inclusion to obtain the required conjugate equation
in the smaller group scheme.

`isFixedVector_of_fppfProduct` applies to an arbitrary matrix representation of
the supplied product. A vector fixed on all tests by both lifted factors is
fixed by the product: the multiplication morphism is epimorphic on schemes,
the representation preserves the ordered product, and the two fixed-vector
equations give fixedness on that epimorphic test. The published epimorphic
fixedness criterion then descends it to all tests.

For `isUnipotent_fppfProduct`, restrict an arbitrary nonzero finite matrix
representation of the product to its lifted factors. Normality of the first
factor transfers through the monic product inclusion. The
`MatrixRepresentation.exists_common_fixedVector` argument constructs a nonzero
vector fixed by both restrictions, using both unipotence assumptions and both
affineness assumptions. The preceding descent lemma makes it fixed by the
product, which is exactly its unipotence.

The proof combines existing factorization, common fixed-vector, and
epimorphic-test results; it invokes no external structural theorem. It
constructs neither the represented product nor the greatest smooth connected
normal unipotent subgroup. Those existence and greatestness obligations in
`UnipotentRadicalExistenceStatement` remain separate.
