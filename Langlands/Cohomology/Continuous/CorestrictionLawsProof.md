# Full continuous corestriction laws

Authors: Worker 22 and Worker 134. Worker 22 supplied the index proof, continuous
tower descent and conjunction assembly; Worker 134 replaced the finite tower
premise with its independently published proof, finalized the unconditional
interfaces and updated the documentation.

`Langlands.Continuous.continuousCorestrictionLaws` proves exactly the unchanged
published proposition `Langlands.Continuous.ContinuousCorestrictionLaws.{u}`.
It has no finite tower, compatibility, index, comparison or other law premise.
The target asserts four identities on Mathlib's actual continuous cohomology
modules after forgetting their topology: compatibility with finite-stage
transfer, naturality for continuous equivariant coefficient maps, restriction
followed by corestriction equal to the subgroup index times the identity, and
transitivity through the explicit subgroup tower coordinate isomorphism.

The imported `continuousCorestrictionCompatibility` supplies the first two
identities. `CorestrictionIndexProof` descends the published ordinary index law
through quotient subgroup coordinates and finite-stage comparison, using normal
core refinements and colimit extensionality. `CorestrictionTowerProof` descends
the published `finiteCorestrictionTower` through its actual coordinate map,
finite-stage corestriction certificates, and the transfer-source comparison
isomorphism. Their paired Markdown gives the implemented calculations.

This module performs only conjunction assembly.
`continuousCorestrictionIndexTower` pairs the index and tower theorems;
`continuousCorestrictionLaws` pairs that result with compatibility. All imported
statements, transfer constructions and subgroup-coordinate maps are unchanged.
The common universe is arbitrary, and the quantified degree ranges over all
natural numbers, including zero. The exact hypotheses remain a commutative ring
with a topology, a compact topological group and a discrete module with jointly
continuous action. No Hausdorff or topological-ring hypothesis is introduced.

The new content is the internal combination and continuous descent of published
results. The mathematical source conventions are inherited from the unchanged
`CorestrictionLawsStatement` and the imported ordinary and finite transfer
proofs. This file makes no additional claim about the source beyond those
published propositions.
