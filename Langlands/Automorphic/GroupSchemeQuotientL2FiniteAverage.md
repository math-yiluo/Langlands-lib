# Compact open averaging on the original quotient L2 space

This internal construction restricts the existing positive right regular action
on `Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i)` along the actual
`AdelicGroupPoints.ofFinite F G` inclusion. The carrier, canonical quotient
measure and its null classes are unchanged. `haarQuotientL2FiniteRightAction`
is that algebraic finite representation; `haarQuotientL2CompactOpenAction`
bundles its original continuous linear maps on an actual open subgroup `K`.

For an actual open subgroup `K` with `[CompactSpace K]`, the subtype
has its original compact topology and Borel sigma algebra. This compactness
assumption is equivalent to `IsCompact (K : Set (FiniteAdelicGroupPoints F G))`
by `isCompact_iff_compactSpace`; consumers may install it from that proof. Its normalized
Haar measure is `compactProbabilityHaar K`, of total mass one. The operator
`haarQuotientL2FiniteAverage` is exactly the Bochner integral of the original
finite orbit over this measure. It is defined on every ambient L2 vector.
The Haar measure used for the group integral is distinct from the canonical
measure defining the quotient L2 norm.

The original continuous orbit map restricts through the continuous finite
inclusion and subgroup inclusion. Norm preservation is inherited from the
original quotient action. Applying `compactIsometricAverage` gives absolute
Bochner integrability, operator norm at most one, output fixed by every
element of `K`, the exact original fixed-vector set and idempotence. These
are direct verifications of the constructed operator.

Output invariance is membership in the published `Langlands.fixedVectors`
submodule for the exact finite representation above. Openness of this same
`K` gives `Langlands.IsSmoothVector` for every output. The continuous linear
`haarQuotientL2FiniteFixedRetraction` has codomain in that existing invariant
submodule. Its inclusion is the average and its restriction to the invariant
submodule is the identity.

The retained assumptions are the number field, affine locally finite-type
group scheme, supplied finite split central torus, injective finite-index
character restriction and norm-one right-Haar invariance needed for the
original canonical quotient action. No connectedness, reductivity or chosen
matrix representation is added. Compactness and openness refer to the
original actual finite adelic point topology.

Provenance is internal: the original quotient representation, orbit map and
bounded action are published constructions; the actual finite inclusion is
from `AdelicGroupProduct`. The probability compact averaging constructor
supplies the analytic integral and retraction identities. This file claims
finite smoothness of these outputs only. Density, convergence as `K` shrinks,
archimedean smoothness, full automorphic tensor realization, admissibility and
spectral decomposition remain further obligations.
