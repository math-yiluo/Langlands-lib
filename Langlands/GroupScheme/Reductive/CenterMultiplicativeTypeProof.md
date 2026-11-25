# Proof of CenterMultiplicativeTypeStatement

`Langlands.GroupScheme.centerMultiplicativeType.{u}` has exactly the published proposition
`Langlands.GroupScheme.CenterMultiplicativeTypeStatement.{u}` as its type. The proposition is defined in
`Langlands.GroupScheme.Reductive.CenterMultiplicativeTypeStatement`.

Every actual full scheme-theoretic center of a connected reductive field group is of multiplicative type, including nonreduced or disconnected centers.

The proof retains the arbitrary published universe `u` and every field and
characteristic allowed by that proposition. It adds no theorem parameter,
structural hypothesis or proposition-valued input. All object-level hypotheses
are exactly those inside the existing target.

The implemented proof is the following direct application of published results:

```lean
centerMultiplicativeTypeCentralizerReduction
    (algClosedMaximalTorusCentralizerReduction dynamicCentralizerReductive
      noTorusUnipotent solvableTorusQuotient)
```

First assemble algebraically closed maximal-torus self-centralization from the three unconditional inputs. Pass that composite directly to the published full-center reduction, which supplies the arbitrary-field multiplicative-type conclusion.

The complete list of reductions and input theorems explicitly used by this term
is below. Every name is a published Library declaration imported by module name.

- `Langlands.GroupScheme.centerMultiplicativeTypeCentralizerReduction` in `Langlands.GroupScheme.Reductive.CenterMultiplicativeTypeReduction`.
- `Langlands.GroupScheme.algClosedMaximalTorusCentralizerReduction` in `Langlands.GroupScheme.Absolute.AlgClosedMaximalTorusCentralizerAssembly`.
- `Langlands.GroupScheme.dynamicCentralizerReductive` in `Langlands.GroupScheme.Dynamic.CentralizerReductiveProof`.
- `Langlands.GroupScheme.noTorusUnipotent` in `Langlands.GroupScheme.Torus.NoTorusUnipotent`.
- `Langlands.GroupScheme.solvableTorusQuotient` in `Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof`.

This is an internal derived proof of the existing Library proposition. The
composite route is also recorded in the note
`notes/group-schemes/composable-targets-2026-11-08.md`.
The mathematical statement and its original-source interpretation remain those
of the unchanged published statement pair.
