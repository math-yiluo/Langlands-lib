# Actual central-quotient topology and coefficient comparison

Author: Worker 117.

This is an internal derived proof of the exact published proposition
`Langlands.Plancherel.CentralSubgroupSquareIntegrabilityComparisonStatement`.
It uses the actual quotient projection, the published compact-kernel Haar/Lp
proof, and the published continuity theorem for actual coefficient norms.
The independent group and representation-carrier universes are retained.

The center inclusion induces a continuous homomorphism from the actual quotient
`Subgroup.center G / A.subgroupOf (Subgroup.center G)` to `G/A`. Its range is
exactly the kernel of `centralQuotientProjection A hA`: on representatives,
`[g]_Z = 1` is equivalent to membership of `g` in the center. Compactness of
the given center quotient therefore makes this actual kernel compact.

The two canonical quotient projections show that the central projection is
surjective and open. Closedness of the center follows by identifying it with
the centralizer of the whole Hausdorff topological group. Closedness of `A`
and of the center supplies Hausdorffness of both quotient groups; quotient
topology also supplies local compactness. The published
`Langlands.compactKernelProperMap` then proves properness.

For the analytic conclusion, second countability descends to the quotients.
The proof applies `Langlands.compactKernelHaarLpMeasure` to the actual central
projection with the two given Borel structures and independently chosen Haar
measures. The full-center coefficient norm is continuous for a smooth vector
by `UnitaryCentralCharacter.continuous_coefficientNorm`; the coefficient norm
on `G/A` is definitionally its pullback. This yields the stated equivalence of
`MemLp` for every extended nonnegative exponent, including zero and infinity,
for each prescribed unitary central character and every algebraic functional.
The generic theorem handles Haar pushforward and positive finite scalar
comparison, so no normalization or measure-preserving premise is required.

Finally, both square-integrability predicates include the same admissibility
condition. Its smoothness component supplies smoothness of every vector.
The exponent-two comparison transfers the coefficient conditions in each
direction, preserving the actual unitary central-character witness and the
quantification over all smooth-dual functionals and all vectors.

This proof introduces no topology on the representation carrier and requires
no irreducibility, finite length, finite dimension, or unitarizability. It is
a generic derived bridge rather than an additional assertion from the
Waldspurger source motivating the statement. It does not construct rational
points of a reductive group, identify a maximal split center, or prove its
closedness or cocompactness in the full center.
