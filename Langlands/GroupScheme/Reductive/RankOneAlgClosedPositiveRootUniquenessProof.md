# Proof of RankOneAlgClosedPositiveRootUniquenessStatement

Authors: Worker 96 and Worker 3483 (identified as Worker 15 in the task context).

`Langlands.GroupScheme.rankOneAlgClosedPositiveRootUniqueness.{u}` has exactly the published proposition
`Langlands.GroupScheme.RankOneAlgClosedPositiveRootUniquenessStatement.{u}` as its type. The proposition is defined in
`Langlands.GroupScheme.Reductive.RankOnePositiveRootBaseChange`.

Over an algebraically closed field, the pairwise integral dependence hypothesis on actual roots of the specified split maximal torus implies uniqueness of a root positive on any specified cocharacter.

The proof retains the arbitrary published universe `u` and every field and
characteristic allowed by that proposition. It adds no theorem parameter,
structural hypothesis or proposition-valued input. All object-level hypotheses
are exactly those inside the existing target.

The implemented proof is the following direct application of published results:

```lean
rankOneAlgClosedPositiveRootUniqueness_of_statement rankOnePositiveRootUniqueness
```

Apply the published restriction from the all-field positive-root theorem to the algebraically closed case, supplying the unconditional all-field proof. Positivity remains the original integer lattice pairing.

The complete list of reductions and input theorems explicitly used by this term
is below. Every name is a published Library declaration imported by module name.

- `Langlands.GroupScheme.rankOneAlgClosedPositiveRootUniqueness_of_statement` in `Langlands.GroupScheme.Reductive.RankOnePositiveRootBaseChange`.
- `Langlands.GroupScheme.rankOnePositiveRootUniqueness` in `Langlands.GroupScheme.Reductive.RankOnePositiveRootProof`.

This is an internal derived proof of the existing Library proposition. Worker 3483 (historical Worker 15)
supplied this composite route in Task 5242's context and the public note
`notes/group-schemes/composable-targets-2026-11-08.md`; Worker 96 checked the
current declarations and authored this separate proof module and explanation.
The mathematical statement and its original-source interpretation remain those
of the unchanged published statement pair.
