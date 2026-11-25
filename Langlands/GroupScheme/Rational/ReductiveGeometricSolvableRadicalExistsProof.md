# Proof of ReductiveGeometricSolvableRadicalExistsStatement

`Langlands.GroupScheme.reductiveGeometricSolvableRadicalExists.{u}` has exactly the published proposition
`Langlands.GroupScheme.ReductiveGeometricSolvableRadicalExistsStatement.{u}` as its type. The proposition is defined in
`Langlands.GroupScheme.Rational.ReductiveGeometricSolvableRadicalExistsStatement`.

Every connected reductive field group admits an actual represented solvable radical that remains a solvable radical after base change to the algebraic closure.

The proof retains the arbitrary published universe `u` and every field and
characteristic allowed by that proposition. It adds no theorem parameter,
structural hypothesis or proposition-valued input. All object-level hypotheses
are exactly those inside the existing target.

The implemented proof is the following direct application of published results:

```lean
reductiveGeometricSolvableRadicalExists_of_structure solvableRadicalExistence
    algClosedReductiveNormalSolvableTorus reductiveLargestCentralSubtorusBaseChange
```

Apply the published structural reduction to unconditional solvable-radical existence, the algebraically closed normal-solvable torus theorem and largest-central-subtorus base change. These discharge the three inputs and give the geometric greatestness required by the original predicate.

The complete list of reductions and input theorems explicitly used by this term
is below. Every name is a published Library declaration imported by module name.

- `Langlands.GroupScheme.reductiveGeometricSolvableRadicalExists_of_structure` in `Langlands.GroupScheme.Rational.ReductiveGeometricSolvableRadicalReduction`.
- `Langlands.GroupScheme.solvableRadicalExistence` in `Langlands.GroupScheme.Rational.SolvableRadicalExistenceProof`.
- `Langlands.GroupScheme.algClosedReductiveNormalSolvableTorus` in `Langlands.GroupScheme.Rational.AlgClosedNormalSolvableTorusProof`.
- `Langlands.GroupScheme.reductiveLargestCentralSubtorusBaseChange` in `Langlands.GroupScheme.Rational.LargestCentralSubtorusBaseChangeProof`.

This is an internal derived proof of the existing Library proposition. The
composite route is the one recorded in the note
`notes/group-schemes/composable-targets-2026-11-08.md`.
The mathematical statement and its original-source interpretation remain those
of the unchanged published statement pair.
