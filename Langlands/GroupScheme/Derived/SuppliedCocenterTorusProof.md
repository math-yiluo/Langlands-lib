# Proof of SuppliedCocenterTorusStatement

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

This is an internal derived proof of the existing Library proposition. The
composite route is recorded in the note
`notes/group-schemes/composable-targets-2026-11-08.md`.
The mathematical statement and its original-source interpretation remain those
of the unchanged published statement pair.
