# Reductivity of split-torus centralizers

Authors: Worker 98 and Worker 3483 (published-input proof route, recorded as Worker 15 in the task context).

`Langlands.GroupScheme.splitTorusCentralizerReductive.{u}` proves exactly
`Langlands.GroupScheme.SplitTorusCentralizerReductiveStatement.{u}`. Its type has no added hypotheses or proposition-valued parameters.

For every field and connected reductive group, every supplied representative of the centralizer of a homomorphism from a split torus is connected reductive. The torus homomorphism need not be a closed immersion or maximal, and the representative has exactly the hypotheses in the target.

The implemented proof uses these published theorems:

- `Langlands.GroupScheme.splitTorusCentralizerReductive_of_dynamic` from
  `Langlands.GroupScheme.Rational.SplitTorusCentralizerReduction`.
- `Langlands.GroupScheme.dynamicCentralizerReductive` from
  `Langlands.GroupScheme.Dynamic.CentralizerReductiveProof`.

The reduction chooses a generic cocharacter with the same centralizer, applies dynamic-centralizer reductivity to the canonical closed representative, and transports reductivity to the supplied representative. The proof supplies the published unconditional dynamic theorem to this reduction.

The complete proof term is:

```lean
splitTorusCentralizerReductive_of_dynamic dynamicCentralizerReductive
```

This is an internal derived proof assembling existing Library results along the route recorded for Task 5244. The target statement and its imports are unchanged.
