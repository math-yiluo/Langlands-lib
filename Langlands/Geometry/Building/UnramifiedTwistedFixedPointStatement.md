# Twisted fixed points from a complete NPC metric

`UnramifiedTwistedFixedPointStatement.{u}` is the fixed-point prerequisite for
`UnramifiedTwistedChamberStatement` at arbitrary universe `u`. The statement
keeps exactly the latter's hypotheses through the cocycle and its finite-level
condition. Its conclusion is existence of a point `y` of the same reduced
building with `c sigma • A.action sigma y = y` for every coefficient automorphism
`sigma`, where `A` is the same `UnramifiedBuildingDescent.semilinearData`.
It does not assert existence of any of the supplied group, torus or apartment
data, and the supplied torus need only have maximal split scalar extension.

The unconditional fixed-point statement remains **unproved** in this pair.
The implemented theorem `unramifiedTwistedFixedPoint_of_metric` proves the
implication from `UnramifiedBuildingMetricStatement.{u}` to that statement.
In particular, the metric existence assertion is an explicit outstanding input,
not an additional hypothesis added to the final twisted-chamber target.

## Implemented reduction

The helper `MaximalUnramified.SemilinearApartmentData.exists_twisted_fixed_point`
accepts a complete NPC metric realization `R` of a semilinear datum `A`, the
cocycle and its law, and a point with a finite orbit under `A.twistedAction`.
It installs the metric, completeness and original rational-point isometry
instances from `R`. The group of coefficient automorphisms acts on the same
carrier via `MulAction.compHom` applied to the previously constructed permutation
homomorphism `A.twistedAction c hc`.

Each twisted transformation is the composition of the isometry `A.action sigma`
with the original isometric translation by `c sigma`. This proves
`IsIsometricSMul` for the twisted action. The given finite orbit is bounded for
this metric, and the given point witnesses nonemptiness. The published theorem
`Langlands.Geometry.Metric.KP.boundedActionFixedPoint` then gives a point fixed
by every twisted transformation. Unfolding the induced action gives precisely
the displayed fixed-point formula. No topology on the acting group or
continuity of its action is needed.

The specialization `unramifiedTwistedFixedPoint_of_metric` applies the assumed
metric-existence statement to the exact data of the fixed-point target. It then
uses `UnramifiedBuildingDescent.exists_finite_twisted_orbit`, with the same
cocycle and finite-fixing-field condition, and applies the preceding helper.
The finite orbit theorem already constructs its coefficient-fixed starting
point using the published unramified fixed-apartment theorem.

## Provenance and scope

This is an internal reduction using the imported constructions and theorems,
rather than a new direct transcription of a literature result. Its route is:
finite twisted orbit, complete NPC isometric action, bounded-action fixed point.
The metric existence input is defined and sourced in the paired
`UnramifiedBuildingMetricStatement` module; its metric and geometric proof
obligations are retained there. The bounded-action fixed-point theorem is the
published proof of KP Corollary 1.1.19. No chamber, special-fibre comparison, or
cocycle-vanishing result enters this reduction.
