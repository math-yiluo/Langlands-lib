# Proof of RankOneAlgClosedBorelExclusionStatement

Authors: Worker 96 and Worker 3483 (identified as Worker 15 in the task context).

`Langlands.GroupScheme.rankOneAlgClosedBorelExclusion.{u}` has exactly the published proposition
`Langlands.GroupScheme.RankOneAlgClosedBorelExclusionStatement.{u}` as its type. The proposition is defined in
`Langlands.GroupScheme.Absolute.RankOneAlgebraicClosureReduction`.

Over an algebraically closed field, a Borel subgroup containing the specified split maximal torus of a connected reductive group has no pair of nonzero actual Lie-image witnesses of opposite root weights.

The proof retains the arbitrary published universe `u` and every field and
characteristic allowed by that proposition. It adds no theorem parameter,
structural hypothesis or proposition-valued input. All object-level hypotheses
are exactly those inside the existing target.

The implemented proof is the following direct application of published results:

```lean
rankOneAlgClosedBorelExclusion_of_geometricStatements rankOneBorelDynamic
    dynamicCentralizerReductive centralizerBorelIntersection
```

Supply the unconditional rank-one Borel dynamics, dynamic centralizer reductivity and centralizer-Borel intersection theorems to the published geometric assembly. This discharges all three premises of the Borel-exclusion reduction.

The complete list of reductions and input theorems explicitly used by this term
is below. Every name is a published Library declaration imported by module name.

- `Langlands.GroupScheme.rankOneAlgClosedBorelExclusion_of_geometricStatements` in `Langlands.GroupScheme.Absolute.RankOneAlgebraicClosureReduction`.
- `Langlands.GroupScheme.rankOneBorelDynamic` in `Langlands.GroupScheme.Reductive.RankOneBorelDynamicProof`.
- `Langlands.GroupScheme.dynamicCentralizerReductive` in `Langlands.GroupScheme.Dynamic.CentralizerReductiveProof`.
- `Langlands.GroupScheme.centralizerBorelIntersection` in `Langlands.GroupScheme.Absolute.CentralizerBorelIntersectionProof`.

This is an internal derived proof of the existing Library proposition. Worker 3483 (historical Worker 15)
supplied this composite route in Task 5242's context and the public note
`notes/group-schemes/composable-targets-2026-11-08.md`; Worker 96 checked the
current declarations and authored this separate proof module and explanation.
The mathematical statement and its original-source interpretation remain those
of the unchanged published statement pair.
