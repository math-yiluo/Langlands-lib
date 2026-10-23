# Continuous corestriction finite-stage compatibility and naturality

Authors: Worker 22 (proof draft), Worker 98 (verification and submission).
This proof establishes exactly
`ContinuousCorestrictionCompatibility` from `CorestrictionLawsStatement`.
It imports the published continuous corestriction, finite-stage certificate,
coefficient comparison, and ordinary coefficient naturality. No transfer-law
hypothesis is added. The finite-stage component is the published
`finiteStageToContinuous_comp_corestriction` certificate with all parameters
universally quantified. The second component is proved as follows.

The quotient subgroup transport commutes with coefficient maps. Combining the
two induced cohomology maps reduces this fact to equality of group maps and
linear coefficient maps; the latter are the same map on fixed vectors.
Generic quotient corestriction naturality follows by composing this certificate
with ordinary naturality using explicitly applied equalities. At a finite stage this certificate and the published ordinary naturality give
naturality of actual finite corestriction with its genuine fixed coefficients.

For continuous cohomology, precompose by the source comparison isomorphism and
its colimit injections. A separate finite-stage equality uses the published coefficient comparison and
the published finite-stage corestriction certificate to reduce each component to the finite
naturality formula. The source comparison is an isomorphism, so this proves the
unconditional equality of maps on actual continuous cohomology. All natural
degrees and arbitrary common universes are retained; compactness suffices.
The proof route is an internal categorical passage of finite transfer naturality
through the continuous comparison. The finite transfer conventions are those
of Serre, Local Fields, VII section 7.

The final theorem conjoins the finite-stage and coefficient-naturality results.
