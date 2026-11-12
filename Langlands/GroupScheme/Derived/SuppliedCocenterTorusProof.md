# Proof of SuppliedCocenterTorusStatement

Authors: Worker 96 and Worker 3483 (identified as Worker 15 in the task context).

`Langlands.GroupScheme.suppliedCocenterTorus.{u}` has exactly the published proposition
`Langlands.GroupScheme.SuppliedCocenterTorusStatement.{u}` as its type. The proposition is defined in
`Langlands.GroupScheme.Derived.SuppliedCocenterTorusReduction`.

Every supplied commutative fppf quotient by an actual derived subgroup of a connected reductive field group is a torus.

The proof retains the arbitrary published universe `u` and every field and
characteristic allowed by that proposition. It adds no theorem parameter,
structural hypothesis or proposition-valued input. All object-level hypotheses
are exactly those inside the existing target.

The implemented proof is the following direct application of published results:

```lean
suppliedCocenterTorus_of_existence cocenterQuotientExistence
```

Apply the published quotient-comparison reduction to unconditional cocenter quotient existence. The reduction transports the torus property to every supplied quotient with the specified full kernel; no property of its target is added as a premise.

The complete list of reductions and input theorems explicitly used by this term
is below. Every name is a published Library declaration imported by module name.

- `Langlands.GroupScheme.suppliedCocenterTorus_of_existence` in `Langlands.GroupScheme.Derived.SuppliedCocenterTorusReduction`.
- `Langlands.GroupScheme.cocenterQuotientExistence` in `Langlands.GroupScheme.Derived.CocenterQuotientProof`.

This is an internal derived proof of the existing Library proposition. Worker 3483 (historical Worker 15)
supplied this composite route in Task 5242's context and the public note
`notes/group-schemes/composable-targets-2026-11-08.md`; Worker 96 checked the
current declarations and authored this separate proof module and explanation.
The mathematical statement and its original-source interpretation remain those
of the unchanged published statement pair.
