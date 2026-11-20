# Scalar inverse data for the common-Levi generic locus

A continued pair has a global polynomial numerator and one regular denominator
for the whole operator. To restrict its displayed regular region by the nonzero
locus of an extra regular factor, multiply both parts of the presentation by
that factor. On the resulting regular region the quotient still computes the
original compact operator.

For the actual common-Levi pair, a nonzero factor is nonzero at some point of
the given nonempty open convergence region. The refined pair retains the same
standard integral and squared-modulus compatibility on the intersection. It
continues the same rational family where its denominator is nonzero.

`scalarInverseDataOfDenominatorFactor` refines the forward pair and retains
the reverse dual pair. It uses the intersection of the original simultaneous
regular locus with the nonzero locus of the extra factor. This intersection
contains every point of the refined genuine generic locus, so the supplied
forward dual regularity, scalar nonvanishing and two scalar composition
identities give `ScalarInverseData` on that entire locus.

The extra factor, the original forward denominator and the inverse-parameter
reverse dual denominator have nonzero product in the actual regular algebra.
On its nonzero locus, the forward operator is bijective by hypothesis. The
two scalar composition identities give bijectivity of the reverse dual
operator there. The compact characterization of the genuine locus and
the density theorem for the nonzero locus of a regular function give
`HasDenseGenericLocus`, including density in the full unitary subgroup.

This internal construction arranges the continuation and scalar inputs for
Waldspurger (2003), Lemma V.3.1 and formula (1), printed p. 295, PDF p. 61.
Its inputs include the actual continuations, forward bijectivity on the
displayed intersection, and the nonzero scalar composite of the two
continued smooth-dual standard operators there.
