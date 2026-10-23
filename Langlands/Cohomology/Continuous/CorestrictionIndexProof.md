# Continuous corestriction index law

Authors: Worker 22 and Worker 134. Worker 22 supplied the finite-stage index
calculation and colimit descent; Worker 134 prepared the final proof unit and
documentation. This module proves the published proposition
`ContinuousCorestrictionIndex` without extra assumptions.

`finiteRestriction_corestriction_index` treats an ambient open normal subgroup
`N` contained in the open subgroup `H`. The published equation
`finiteRestriction_quotientSubgroupCohomologyIso` converts finite restriction
followed by the quotient subgroup coordinate isomorphism into ordinary
restriction for the image of `H` in `G/N`. Unfolding finite corestriction then
exposes ordinary restriction followed by ordinary transfer. The index component
of the published `ordinaryTransferLaws` applies in every natural degree. The
quotient projection is surjective and its kernel is contained in `H`, so
`Subgroup.index_map_eq` identifies the image subgroup index with `H.index`.
Finiteness and the required finite-type instances are derived from the compact
group and its open normal subgroup.

`continuousRestriction_corestriction_index` first precomposes the desired
continuous equality with inflation from a stage contained in `H`. The published
restriction comparison and finite-stage corestriction certificate reduce that
composite to the finite index formula. The natural-number multiple of the
identity commutes with composition because `ModuleCat` is preadditive.

For an arbitrary normal stage `N`, intersect `N` with `ambientOpenNormalCore H`.
This refinement is contained in `H`. Precomposing its stage equality with finite
inflation and using `finiteStageToContinuous_refinement` gives the equality at
`N`. Cancel the epimorphism `finiteQuotientComparison A q` and apply colimit
extensionality to conclude equality on the actual continuous cohomology object,
with topology forgotten. The final theorem `continuousCorestrictionIndex`
universally quantifies this result to match the published proposition exactly.

The arbitrary common universe and all natural degrees, including zero, are
retained. The assumptions are a commutative ring with topology, a compact
topological group, and discrete coefficients with jointly continuous action;
no Hausdorff or topological-ring hypothesis is introduced. The actual
restriction, transfer and quotient-coordinate maps are the published ones.

This is a derived internal proof through the published finite-quotient
comparison. Its index-law provenance is inherited from
`CorestrictionLawsStatement` and `OrdinaryTransferLawsProof`, whose paired
Markdown records Serre's norm and index conventions. The implemented proof is
the finite-stage and colimit argument above; it does not reproduce the ordinary
transfer proof.
