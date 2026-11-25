# Continuity on compact analytic pullbacks

**Not to be used.** Do not use `CompactPullbackActionContinuityStatement` as a
target or as a premise. It is replaced by
`CompactPullbackActionContinuitySmallStatement` in
`Langlands.Geometry.Analytic.CompactPullbackActionContinuitySmall`. That statement
adds the explicit hypothesis
`∀ R : PresentedAffinoidAlgebra K, Small.{v} (BanachSpectrum R)`. Without it, the
pair chart of a pullback need not be an object of `LocalizedCategory.{u,v,v}`
when the field `K : Type u` is not `v`-small; the replacement's Markdown gives the
trivially valued example. In general this proposition is neither proved nor
refuted; under `UnivLE.{u, v}` it is proved by
`compactPullbackActionContinuityStatement_of_univLE` in
`Langlands.Geometry.Analytic.CompactPullbackContinuityOfSmall`. Its Lean text is
left unchanged.

`CompactPullbackActionContinuityStatement` is an internal analytic prerequisite
for the finite tuple-cone construction. It defines a proposition and does
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
