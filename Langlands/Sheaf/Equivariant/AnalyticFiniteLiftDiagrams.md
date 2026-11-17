# Common subgroup actions for finite diagrams of compact analytic lifts

This internal construction turns the explicit premise
`HasCompatibleCompactQuasiEtaleLifts rho` into simultaneous equivariance for
a finite family of ordinary quasi-etale-site arrows. It does not prove that
premise, construct analytic fibre products, or establish a cohomology comparison.

Let `U : I -> QuasiEtaleSite X` be a family of objects, each equipped with an
`ActionLift rho`, and let arrows be indexed by `E`, with specified source and
target in `I`. `CommonEquivariantLiftDiagram` records an open subgroup contained
in a prescribed bound `Q` and every vertex's acting subgroup, on which every
specified arrow intertwines its source and target actions. The structure does
not require `I` or `E` to be finite; the existence theorem does.

`nonempty_commonEquivariantLiftDiagram` assumes finite vertex and arrow index
types, compact Hausdorffness of every vertex, and compact-lift compatibility.
Apply compatibility to each arrow and its two supplied lifts. Intersect these
finitely many open subgroups with all vertex subgroups and `Q`. Each intertwining
equation restricts to the resulting subgroup. Including all vertex subgroups
ensures that isolated vertices are covered, even when there are no arrows.
Empty index types, repeated arrows and loops are allowed.
`commonEquivariantLiftDiagram` chooses this data.

The structure's `shrink` construction retains all equations on any smaller open
subgroup. This permits a later choice of subgroup fixing coefficient sections.
`restrictedLift` uses the existing `ActionLift.restrict`, retaining its actual
continuous analytic action. `globalLift` uses the published `liftGlobalLift` to
normalize these actions for the common subgroup. `globalLift_equivariant` checks
the corresponding equality in the actual twisted site; its proof applies the
ordinary intertwining equation to the inverse of the group element, as required
by the inverse twist convention. Finally,
`globalLift_eventuallyEquivariant` applies the existing analytic compact-lift
compatibility adapter to each vertex.

The construction is uniform in `LocalizedCategory.{u,v,v}`, the independent
group universe and the two index universes. It uses no topological-group
instance, global continuity of `rho`, compactness of `X`, finite equivariant
refinement hypothesis, or coefficient data. Continuity is retained in each
supplied action lift, while compatibility remains an explicit premise.

The provenance is internal: finite intersections of the open subgroups supplied
by `HasCompatibleCompactQuasiEtaleLifts`, together with the published analytic
restriction and normalization constructions, give exactly the recorded data.
One application is to finite portions of a tuple-cone diagram, after the
existence of its compact lifted cone points and ordinary arrows has been proved.
