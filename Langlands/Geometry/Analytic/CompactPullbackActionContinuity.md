# Continuity on compact analytic pullbacks

`CompactPullbackActionContinuityStatement` is an internal analytic prerequisite
for the tuple-cone construction of Task 7491. It defines a proposition and does
not prove continuity.

Fix a complete ultrametric normed field `K : Type u` and a group `G : Type z`
carrying a topology. Let `P → U`, `P → V`, `U → B`, and `V → B` form an actual
categorical pullback in `LocalizedCategory.{u,v,v}`. All four analytic spaces
are assumed compact and Hausdorff. Suppose `G` acts by analytic automorphisms
on `P`, `U`, and `V`; the actions on `U` and `V` are continuous in the Library's
Berkovich test-triple sense `IsContinuousAction`. If both pullback projections
are equivariant as full analytic morphisms, the statement asks that the supplied
action on `P` satisfy the same `IsContinuousAction` condition.

No topological-group instance is required. No action on `B` is part of this
continuity assertion: a separate categorical construction can use an action on
`B` to produce the action on `P`. The statement does not identify analytic
pullback points with pairs of points of the factors. Its categorical pullback
hypothesis is the full localized universal property, not a pointwise condition.

Provenance: this internal prerequisite isolates the analytic continuity step in
constructing finite tuple cones from compatible continuous actions. Induction
uses it with the common open subgroup of the given compatible cover as `G`.
The already supplied cover actions are restricted to that subgroup. This
statement neither invokes action-lift uniqueness nor presumes an unproved Key
Lemma, and it is not claimed to be a direct transcription of a cited source.
