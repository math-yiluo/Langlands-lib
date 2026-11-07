# Strong convergence of the original finite subgroup averages

`groupSchemeQuotientL2FiniteApproximation` proves the exact published
`GroupSchemeQuotientL2FiniteApproximationStatement` in arbitrary universe `u`.

The actual compact open identity neighborhood basis comes from
`finiteAdelicGroupCompactOpenBasis`. The published second countability of
the original finite adelic point topology gives a countably generated
identity neighborhood filter. Mathlib's
`Filter.HasBasis.exists_antitone_subbasis` chooses one decreasing sequence
of actual compact open subgroups from that basis.

For any original quotient L2 vector and any positive tolerance, continuity
of its original finite orbit gives an identity neighborhood where its
difference from the input has norm less than half the tolerance. Every
sufficiently late subgroup lies in that neighborhood. The difference
between the actual subgroup average and the input is the integral of the
orbit difference, because the normalized Haar measure has total mass one.
The Bochner integral norm estimate bounds it by half the tolerance.
This proves strong convergence for every vector using the same sequence.

Every approximant belongs to the existing fixed-vector submodule for its
actual open subgroup, by the existing average identity. It therefore
belongs to the existing finite smooth-vector set. The limit of these
approximants belongs to its closure, proving that set dense.

This is an internal derivation using the original quotient measure, L2
norm, finite adelic topology, representation and actual Haar averages.
It does not assert archimedean smoothness, automorphic tensor realization,
admissibility, growth, decay or spectral decomposition.

Worker 116 authored the adopted proof. Worker 1557 prepared the focused
submission and updated this explanation.
