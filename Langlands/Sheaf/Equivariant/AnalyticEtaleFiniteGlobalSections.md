# Étale global sections under finite base subcovers

This derived internal construction specializes
`TwistedFiniteGlobalInclusion` to the analytic étale site and the published
canonical map `etaleGlobalInclusion`.

Let a topological group `G` act by automorphisms `ρ` on an analytic space `X`.
Assume `HasFiniteBaseSubcovers (twistedEtaleTopology ρ)`: every covering sieve
at the twisted base contains a finite family whose generated sieve covers.
Then `isIso_etaleGlobalInclusion_of_finiteBaseSubcovers` proves that
`etaleGlobalInclusion ρ R` is an isomorphism for any commutative coefficient
ring in the universes of the published étale cohomology construction.

The proof applies `isIso_exactGlobalInclusion_of_locallyDiscrete` to the
inclusion of étale `G`-sheaves into sheaves on the twisted étale site.
An étale `G`-sheaf has local discreteness as its defining property.
The distinguished local-action system is a `liftSystem`, so the published
`isLiftSystem_liftSystem` supplies the remaining lifted-action hypothesis.

`etaleFiniteGlobalSectionsIso` packages this result as a natural isomorphism
between the underlying modules of smooth global sections and all global
sections of the restriction. Its forward transformation is exactly
`etaleGlobalInclusion`, as recorded by `etaleFiniteGlobalSectionsIso_hom`.

The finite-cover hypothesis remains explicit. This construction neither
proves that compact analytic spaces satisfy it nor asserts the isomorphism
of the higher-degree comparison maps. It requires no smallness of `G`,
admissible-refinement hypothesis, or continuity of the analytic action
beyond the hypotheses already stated: those are not used in this
degree-zero specialization.
