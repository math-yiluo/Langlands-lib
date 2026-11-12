# Proof of SemisimpleNormalRootDichotomyStatement

Authors: Worker 96 and Worker 3483 (identified as Worker 15 in the task context).

`Langlands.GroupScheme.semisimpleNormalRootDichotomy.{u}` has exactly the published proposition
`Langlands.GroupScheme.SemisimpleNormalRootDichotomyStatement.{u}` as its type. The proposition is defined in
`Langlands.GroupScheme.Reductive.NormalRootDichotomyStatement`.

For a smooth connected normal closed subgroup of a semisimple group over an algebraically closed field, each actual root subgroup of the specified split maximal torus is contained in that subgroup or centralizes it on every test and refinement.

The proof retains the arbitrary published universe `u` and every field and
characteristic allowed by that proposition. It adds no theorem parameter,
structural hypothesis or proposition-valued input. All object-level hypotheses
are exactly those inside the existing target.

The implemented proof is the following direct application of published results:

```lean
semisimpleNormalRootDichotomy_of_rootLines normalReductiveCenter
    (semisimpleRootGenerationReduction rootRankOneFactorization
      (algClosedMaximalTorusCentralizerReduction dynamicCentralizerReductive
        noTorusUnipotent solvableTorusQuotient))
    absoluteRootVectorLine maximalTorusConjugacy
```

The inline root-generation term combines rank-one factorization with the assembled maximal-torus self-centralization. Supply that term, the unconditional normal-center theorem, actual root-vector line theorem and maximal-torus conjugacy theorem to the published root-line dichotomy reduction.

The complete list of reductions and input theorems explicitly used by this term
is below. Every name is a published Library declaration imported by module name.

- `Langlands.GroupScheme.semisimpleNormalRootDichotomy_of_rootLines` in `Langlands.GroupScheme.Reductive.NormalRootDichotomyReduction`.
- `Langlands.GroupScheme.normalReductiveCenter` in `Langlands.GroupScheme.Reductive.NormalCenterProof`.
- `Langlands.GroupScheme.semisimpleRootGenerationReduction` in `Langlands.GroupScheme.Reductive.RootGenerationReduction`.
- `Langlands.GroupScheme.rootRankOneFactorization` in `Langlands.GroupScheme.Rational.RootRankOneFactorizationProof`.
- `Langlands.GroupScheme.algClosedMaximalTorusCentralizerReduction` in `Langlands.GroupScheme.Absolute.AlgClosedMaximalTorusCentralizerAssembly`.
- `Langlands.GroupScheme.dynamicCentralizerReductive` in `Langlands.GroupScheme.Dynamic.CentralizerReductiveProof`.
- `Langlands.GroupScheme.noTorusUnipotent` in `Langlands.GroupScheme.Torus.NoTorusUnipotent`.
- `Langlands.GroupScheme.solvableTorusQuotient` in `Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof`.
- `Langlands.GroupScheme.absoluteRootVectorLine` in `Langlands.GroupScheme.Absolute.RootVectorLineProof`.
- `Langlands.GroupScheme.maximalTorusConjugacy` in `Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof`.

This is an internal derived proof of the existing Library proposition. Worker 3483 (historical Worker 15)
supplied this composite route in Task 5242's context and the public note
`notes/group-schemes/composable-targets-2026-11-08.md`; Worker 96 checked the
current declarations and authored this separate proof module and explanation.
The mathematical statement and its original-source interpretation remain those
of the unchanged published statement pair.
