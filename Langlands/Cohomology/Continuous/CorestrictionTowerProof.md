# Continuous corestriction tower law

Authors: Worker 22 and Worker 134. Worker 22 supplied the continuous descent
argument; Worker 134 discharged its finite tower premise using the published
`finiteCorestrictionTower` and prepared the unconditional theorem and
documentation. This module proves `ContinuousCorestrictionTower` with no
additional law assumption.

For open subgroups `K ≤ H ≤ G`, `continuousCorestriction_tower` equates direct
transfer from `K` to `G` with the composite of the actual continuous tower
coordinate isomorphism, transfer from `towerOpenSubgroup K H` to `H`, and
transfer from `H` to `G`. The compactness instance for `H` is derived from its
closedness in compact `G`.

At an ambient open normal stage `N ≤ K`, finite-stage corestriction
compatibility for `K` reduces the left side to finite transfer followed by
ambient inflation. Apply the independently published `finiteCorestrictionTower`
to factor this finite transfer into `finiteTowerCohomology`, transfer inside
`H`, and transfer from `H` to `G`. The finite-stage corestriction certificates
inside `H` and from `H` to `G` identify this with the corresponding continuous
transfers after subgroup inflation. Finally,
`finiteTowerCohomology_comp_stage` replaces the finite coordinate map and
inflation by inflation followed by the actual `continuousTowerCohomologyIso`.
The three composed equalities are reassociated to yield the stage equation.

To pass to all continuous cohomology, precompose with the homomorphism of
`transferSourceComparisonIso A K q`, which is an epimorphism, and apply colimit
extensionality. The injection at an indexing subgroup `N` becomes the continuous
inflation at `ambientOpenNormalCore K ⊓ N` by
`transferSourceComparisonIso_ι`. This subgroup lies in `K`, so the proved stage
equality applies. Cancelling the comparison yields the desired equality.
`continuousCorestrictionTower` universally quantifies it to prove the exact
published proposition.

All natural degrees, including zero, and the arbitrary common universe are
retained. The commutative scalar ring has a topology, the ambient group is
compact, and the coefficient module is discrete with jointly continuous action.
Neither a Hausdorff nor a topological-ring assumption is added. The explicit
subgroup carrier and coefficient transports are retained unchanged.

This is an internal descent through published finite-stage comparison results.
The finite transfer conventions and derived norm-composition provenance are
recorded in `CorestrictionLawsStatement` and `FiniteCorestrictionTowerProof`.
The latter is imported by Lean name; this module proves the continuous passage,
not a new finite quotient-coordinate calculation.
