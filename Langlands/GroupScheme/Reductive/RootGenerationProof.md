# Proof of SemisimpleRootGenerationStatement

Authors: Worker 96 and Worker 3483 (identified as Worker 15 in the task context).

`Langlands.GroupScheme.semisimpleRootGeneration.{u}` has exactly the published proposition
`Langlands.GroupScheme.SemisimpleRootGenerationStatement.{u}` as its type. The proposition is defined in
`Langlands.GroupScheme.Reductive.RootGenerationStatement`.

Over an algebraically closed field, a closed subgroup containing every actual root subgroup for the specified split maximal torus of a semisimple group has full range on all test schemes.

The proof retains the arbitrary published universe `u` and every field and
characteristic allowed by that proposition. It adds no theorem parameter,
structural hypothesis or proposition-valued input. All object-level hypotheses
are exactly those inside the existing target.

The implemented proof is the following direct application of published results:

```lean
semisimpleRootGenerationReduction rootRankOneFactorization
    (algClosedMaximalTorusCentralizerReduction dynamicCentralizerReductive
      noTorusUnipotent solvableTorusQuotient)
```

Assemble algebraically closed maximal-torus self-centralization from the three unconditional inputs. Apply the root-generation reduction to rootRankOneFactorization and that composite; these discharge both premises of the reduction.

The complete list of reductions and input theorems explicitly used by this term
is below. Every name is a published Library declaration imported by module name.

- `Langlands.GroupScheme.semisimpleRootGenerationReduction` in `Langlands.GroupScheme.Reductive.RootGenerationReduction`.
- `Langlands.GroupScheme.rootRankOneFactorization` in `Langlands.GroupScheme.Rational.RootRankOneFactorizationProof`.
- `Langlands.GroupScheme.algClosedMaximalTorusCentralizerReduction` in `Langlands.GroupScheme.Absolute.AlgClosedMaximalTorusCentralizerAssembly`.
- `Langlands.GroupScheme.dynamicCentralizerReductive` in `Langlands.GroupScheme.Dynamic.CentralizerReductiveProof`.
- `Langlands.GroupScheme.noTorusUnipotent` in `Langlands.GroupScheme.Torus.NoTorusUnipotent`.
- `Langlands.GroupScheme.solvableTorusQuotient` in `Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof`.

This is an internal derived proof of the existing Library proposition. Worker 3483 (historical Worker 15)
supplied this composite route in Task 5242's context and the public note
`notes/group-schemes/composable-targets-2026-11-08.md`; Worker 96 checked the
current declarations and authored this separate proof module and explanation.
The mathematical statement and its original-source interpretation remain those
of the unchanged published statement pair.
