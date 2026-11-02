# Strict tests and rational neighborhoods under bounded equivalences

This internal supporting comparison starts with a full represented domain `U`
over a generalized affinoid presentation `A`, and actual bounded algebra
equivalences `eA : A ≃ P` and `eU : U.algebra ≃ Q` to strict presentations over
the same complete ultrametric coefficient field `K : Type u`.

`strictMap` conjugates the structural map through these equivalences.
`strictLocus` is the inverse image of the original locus under the ambient
spectrum homeomorphism. `strictMap_spectrum` proves the exact commutative
spectrum triangle by the inverse identity for `eA`.

`strictRepresents` proves strict-test representation of this closed subset.
Closedness is continuous inverse image of the original closed locus. Exact
spectrum image follows from the triangle, the original exact spectrum image,
and surjectivity of the domain-algebra spectrum homeomorphism. For an arbitrary
strict test `R`, `ofStrict K R` and its actual bounded comparison to `R`
give a generalized test. The full domain universal property supplies its unique
bounded factor. Conjugation produces the required strict factor and its
structural equation. Any competing factor conjugates back to the same
generalized test, so the original uniqueness proves equality.

`strictLocusHomeomorph` is the restriction of the ambient spectrum homeomorphism
to these two actual loci. `chartOfStrict` sends strict rational coefficient
classes through `eA`'s inverse and chooses weighted-series representatives in
the original ambient presentation. All its rational radii are one. Unit-ideal
generation is the image under that inverse algebra map of the strict rational
data's proved unit-ideal generation; it is not an additional hypothesis.
`chartOfStrict_locus` proves exact equality with the inverse image of the
strict rational inequalities.

`neighborhoodOfStrict` transports a strict rational locus contained in the
strict represented locus, with its relative-neighborhood hypothesis, into a
`Domain.RationalNeighborhood U x`. The locus identity and the homeomorphism
prove containment and the subspace-neighborhood condition. The full original
domain property constructs the actual bounded restriction into `U` from that
containment. `nonempty_rationalNeighborhood_of_strict` applies a supplied
`StrictTestDomain.LocalRationalNeighborhoodStatement` over a nontrivially
valued field to obtain these input data.

The provenance is internal transport of actual bounded maps, quotient
presentations, multiplicative spectra, unit ideals and subspace neighborhoods.
No local Gerritzen–Grauert theorem is proved here: it is an explicit hypothesis
of the last theorem. No nontriviality is needed for the preceding comparisons.
Zero and nonreduced quotients, empty coordinate tuples and empty loci are
retained. The host full finite rational-cover theorem remains separate.
