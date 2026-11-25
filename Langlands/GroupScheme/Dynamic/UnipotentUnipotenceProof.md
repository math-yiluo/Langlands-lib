# Proof of DynamicUnipotentUnipotenceStatement

`Langlands.GroupScheme.dynamicUnipotentUnipotence.{u}` has exactly the published proposition
`Langlands.GroupScheme.DynamicUnipotentUnipotenceStatement.{u}` as its type. The proposition is defined in
`Langlands.GroupScheme.Dynamic.UnipotentUnipotenceStatement`.

Every actual representative of the dynamic unipotent subgroup of an affine locally finite-type field group is unipotent in the published representation-theoretic sense.

The proof retains the arbitrary published universe `u` and every field and
characteristic allowed by that proposition. It adds no theorem parameter,
structural hypothesis or proposition-valued input. All object-level hypotheses
are exactly those inside the existing target.

The implemented proof is the following direct application of published results:

```lean
dynamicUnipotentUnipotenceReduction unitriangularUnipotent unipotentClosedSubgroup
```

Apply the published dynamic-unipotence reduction to unconditional unitriangular unipotence and inheritance of unipotence by closed subgroups. Both structural inputs are thereby discharged for every supplied representative.

The complete list of reductions and input theorems explicitly used by this term
is below. Every name is a published Library declaration imported by module name.

- `Langlands.GroupScheme.dynamicUnipotentUnipotenceReduction` in `Langlands.GroupScheme.Dynamic.UnipotentUnipotenceReduction`.
- `Langlands.GroupScheme.unitriangularUnipotent` in `Langlands.GroupScheme.UnitriangularUnipotentProof`.
- `Langlands.GroupScheme.unipotentClosedSubgroup` in `Langlands.GroupScheme.UnipotentClosedSubgroupProof`.

This is an internal derived proof of the existing Library proposition. The
composite route is also recorded in the public note
`notes/group-schemes/composable-targets-2026-11-08.md`.
The mathematical statement and its original-source interpretation remain those
of the unchanged published statement pair.
