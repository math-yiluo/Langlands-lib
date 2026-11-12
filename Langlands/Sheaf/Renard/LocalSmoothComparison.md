# Comparing the two smoothness conditions

Worker 151. Internal construction supporting Renard III.3.2 restriction,
printed p.84 / PDF p.90 of the 9 July 2026 edition. It compares Renard
III.3.1 smoothness of all compact sections (p.83 / PDF p.89) with the
published local smoothness predicate; the local formulation is an
implementation tool, not a separate assertion attributed to Renard.

The group has an independent universe. The base, complex coefficients and
section carriers are in `Type`, as required by the existing compact-section
interface. The action is jointly continuous. The comparison assumes the
original Hausdorff locally profinite base and stable neighbourhoods.

`isLocallyFixedAt_of_globalFixed` intersects a global section's open fixing
subgroup with an open subgroup stabilizing a smaller neighbourhood.
Functoriality of the original transport arrows proves local fixedness.
`isSmoothSheaf_of_isSmoothAction` restricts an original local section to a
compact open and uses the published `CompactGerms.compactExtension`.
Smoothness fixes this actual compact global section, and its restriction
recovers the original section on that compact open.

`isSmoothAction_iff_isSmoothSheaf` combines this direction with the
published compactness argument
`CompactSections.isSmooth_representation_of_isSmoothSheaf`.
`localSmoothEquivalence` restricts the identity equivalence of the original
action-sheaf category using that equivalence of predicates. It changes
only property proofs; its underlying sheaves and morphisms are retained.

`hasStableNeighbourhoods_of_locallyProfinite` obtains the nonarchimedean
group structure from the published Van Dantzig theorem, then applies the
existing stable-neighbourhood instance. Thus, for Renard's Hausdorff t.d.
topological groups, stable neighbourhoods are derived rather than an
additional source hypothesis. No countability assumption is used here.

The general smooth inverse-image functor and its comparison with ordinary
sheaf restriction remain separate constructions.
