# Actual orbit coefficients and flattened Jacquet quotients

Author: Worker 194.

This internal prerequisite identifies the genuine nested radical coinvariants
of the orbit coefficient for normalized induction of normalized Jacquet
restriction with an actual flattened Jacquet quotient. The supplied
`IsIntersectionRefinement B C w S` identifies the three actual source
intersection subgroups with the standard product refinement `S`.

`iteratedFlattenedJacquetEquiv` composes the published natural normalized
Jacquet transitivity isomorphism with the published normalized comparison of
the composed radical and the flattened radical. The first map takes the
iterated class of an original vector to its class for the composed radical;
the second takes that class to its ordinary flattened Jacquet class.
`iteratedFlattenedJacquetEquiv_mk` proves this representative formula.

`cutOrbitCoefficientJacquetEquiv` first applies the actual nested coefficient
comparison. That comparison removes the redundant stages subgroup, identifies
the genuine radical image with the source intersection, and cancels the
positive inducing half character on its unipotent radical. It then applies
the preceding iterated-to-flattened quotient equivalence.
`cutOrbitCoefficientJacquetEquiv_mk_mk` records that the nested class of the
source Jacquet class of `v` is sent to the flattened Jacquet class of `v`.
All these maps act on the actual quotient carriers.

`cutOrbitCoefficient_subsingleton_of_flattened` transfers vanishing of the
flattened Jacquet quotient to the actual nested orbit coefficient by
injectivity of this equivalence.

The provenance is internal: the proofs compose existing actual quotient
comparisons and their representative formulas. This is a linear equivalence
of coefficient carriers; it asserts no equality of orbit actions and no
identification of the complete graded cut diagram or its homology. The field
and representation universes remain independent, and no positive-rank
assumption is imposed.
