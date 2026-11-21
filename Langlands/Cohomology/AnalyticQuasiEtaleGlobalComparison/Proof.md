# Proof of the compact quasi-étale global comparison

`analyticQuasiEtaleGlobalComparison` proves the Library proposition for the
quasi-étale case of Berkovich's Theorem 1.6.1(ii). It applies
`analyticQuasiEtaleGlobalComparison_of_tupleCones_liftCompatibilityStatement`
to two published theorems. `compactCompatibleTupleCones` supplies limiting
cones in the quasi-étale site for every positive tuple of a compatible compact
cover. Each vertex is compact Hausdorff and carries a continuous action lift
on an open subgroup. `quasiEtaleLiftCompatibility K` gives compatibility of
the chosen lifts along a morphism over the base after restriction to a common
open subgroup. The reduction obtains the Hausdorff hypothesis for
compatibility from compactness of `X`.

The tuple cones give the Čech presentations used to prove higher acyclicity
of the ordinary restrictions of injective equivariant sheaves. Together with
the degree-zero isomorphism on global sections, this gives an isomorphism of
the specified derived comparison natural transformation in every degree.
The smallness and finite equivariant refinement instances are those of
`AnalyticQuasiEtaleGlobalComparisonStatement`.
