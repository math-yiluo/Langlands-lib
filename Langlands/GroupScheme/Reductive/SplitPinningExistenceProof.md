# Proof of SplitPinningExistenceStatement

Authors: Worker 96 and Worker 3483 (identified as Worker 15 in the task context).

`Langlands.GroupScheme.splitPinningExistence.{u}` has exactly the published proposition
`Langlands.GroupScheme.SplitPinningExistenceStatement.{u}` as its type. The proposition is defined in
`Langlands.GroupScheme.Reductive.PinningExistenceStatement`.

A connected reductive field group with a supplied split maximal torus admits a SplitPinning, including a finite reduced root datum, a base and actual simple-root Lie trivializations.

The proof retains the arbitrary published universe `u` and every field and
characteristic allowed by that proposition. It adds no theorem parameter,
structural hypothesis or proposition-valued input. All object-level hypotheses
are exactly those inside the existing target.

The implemented proof is the following direct application of published results:

```lean
splitPinningExistence_of_rootDatumExistence rootDatumExistence
```

Apply the published pinning construction reduction to the unconditional root-datum existence theorem. The reduction already supplies the simple-root trivializations and choice of base, so no root datum or pinning is added as a premise.

The complete list of reductions and input theorems explicitly used by this term
is below. Every name is a published Library declaration imported by module name.

- `Langlands.GroupScheme.splitPinningExistence_of_rootDatumExistence` in `Langlands.GroupScheme.Reductive.RootPinningFromSplitTorus`.
- `Langlands.GroupScheme.rootDatumExistence` in `Langlands.GroupScheme.Reductive.RootDatumExistence`.

This is an internal derived proof of the existing Library proposition. Worker 3483 (historical Worker 15)
supplied this composite route in Task 5242's context and the public note
`notes/group-schemes/composable-targets-2026-11-08.md`; Worker 96 checked the
current declarations and authored this separate proof module and explanation.
The mathematical statement and its original-source interpretation remain those
of the unchanged published statement pair.
