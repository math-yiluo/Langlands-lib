# Round trips for a system of continued compact standard operators

`CompactContinuationSystem` keeps the actual compact continuations for
all ordered pairs with a common Levi and common compact. Its value on
an operator denominator's nonzero set is the original continued value.
Admissible irreducible unitary inducing data give a system through
`continuedPairOfUnitarizable`.

`exists_compactContinuationValue_comp_smul` expresses distance-additive
composition using `exists_continuedPair_comp_smul` at the original quotient
measures. `compactContinuationValue_roundTrip_isScalar` applies
`continuedInductionComposite_generic_scalar` at a regular irreducible fiber.
For two opposite pairs, `exists_opposite_roundTrip_scale` uses four triples
with opposite endpoints and cancels the nonzero cross operator by
`oppositeScalar_mul_of_scaled_composition`. The proportionality factor is a
positive product and quotient of the specified Haar factors. This is the
compact-operator calculation in Waldspurger IV.3(1), printed pp. 285–286.
`exists_opposite_roundTrip_product` factors the scalar through both ordered
pairs at an intermediate parabolic, as in IV.3(4), printed p. 286.

`exists_gallery_roundTrip_product` combines the comparison of two
opposite pairs with the factorization through a third parabolic. The
outer round trips based at the two endpoints have the same scalar when
the forward compact operator is surjective, by evaluating on its image.
