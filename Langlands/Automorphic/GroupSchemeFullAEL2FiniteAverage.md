# Compact open averaging on the original full cusp L2 space

This internal construction restricts `fullAEL2CuspidalRightAction` along the
actual `AdelicGroupPoints.ofFinite` inclusion and then to an actual open
subgroup `K` of the finite adelic point group. The original full cuspidal
submodule, canonical positive quotient measure and inherited Hilbert norm
are unchanged. The cusp condition still requires separate almost-everywhere
absolute convergence and vanishing of periods for every actual proper
rational parabolic.

With `[CompactSpace K]`, equivalent to compactness of the original underlying
set of `K`, the operator `fullAEL2CuspidalFiniteAverage` is the Bochner integral
of this original orbit against `compactProbabilityHaar K`. The subtype has
its inherited topology and Borel sigma algebra. Its topological group and
second countability properties are inherited from the actual finite adelic
group, and completeness of the cusp codomain follows from its published
closedness in the original ambient L2 space. No smoothness is required of
the input.

The normalized probability Haar integral is absolutely convergent on every
cusp vector, has operator norm at most one, is fixed by every element of
`K`, fixes exactly the original `K`-invariant vectors and is idempotent.
Output invariance is membership in the existing `Langlands.fixedVectors`
for the restricted finite representation. This supplies
`Langlands.IsSmoothVector` and a continuous linear retraction into that
existing invariant submodule. These are direct verifications of the
constructed operator.

The generic continuous intertwiner law identifies the average under the
original faithful cusp inclusion with `haarQuotientL2FiniteAverage` on the
ambient quotient. Consequently the ambient operator preserves the full
cusp submodule. The same law for the original subtype-valued orthogonal
projection gives its exact intertwining identity; composing with the
inclusion gives commutation of the original ambient cusp projection with
the ambient finite average. The subgroup and its normalized Haar measure
are the same in all these identities.

All hypotheses of the original cusp construction remain: number field,
affine locally finite-type group scheme, connected reductivity, structural
`ParabolicDynamicStatement`, the supplied finite split central torus,
injective finite-index character restriction and norm-one right-Haar
invariance. No extra continuity, closedness or completeness assumption is
introduced. There is no replacement automorphic space or point topology.

Provenance is internal. The original cusp Hilbert action and its inclusion
and orthogonal projection laws are published constructions. The normalized
compact average is supplied by `CompactIsometricAverage`; the ambient
specialization is `GroupSchemeQuotientL2FiniteAverage`. This file proves
finite smoothness of the outputs and compatibility of actual operators.
It claims no density, convergence as subgroups shrink, archimedean
smoothness, automorphic tensor realization, trace or spectral decomposition.
