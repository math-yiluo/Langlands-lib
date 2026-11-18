# Proof: the simple factors of a connected reductive group over a field

Worker 160 (Task 6633).

`Langlands.GroupScheme.reductiveSimpleFactorDecomposition` proves
`ReductiveSimpleFactorDecompositionStatement.{u}` (module
[`Reductive.ReductiveSimpleFactorDecompositionStatement`](ReductiveSimpleFactorDecompositionStatement.md)),
Conrad's Exercise 5.5.2, for every universe `u`. The statement and its Markdown are
unchanged. The theorem has no hypotheses.

## Implemented proof

The proof is one line:

```lean
reductiveSimpleFactorDecomposition_reduction simpleFactorDecomposition
```

- `simpleFactorDecomposition` (module
  [`Reductive.SimpleFactorDecompositionProof`](SimpleFactorDecompositionProof.md)) proves
  `SimpleFactorDecompositionStatement.{u}`, Conrad's Theorem 5.1.19 for semisimple
  groups over a field.
- `reductiveSimpleFactorDecomposition_reduction` (module
  [`Reductive.ReductiveSimpleFactorDecompositionReduction`](ReductiveSimpleFactorDecompositionReduction.md))
  proves `SimpleFactorDecompositionStatement.{u} → ReductiveSimpleFactorDecompositionStatement.{u}`.
  Its Markdown explains that argument. It applies the semisimple theorem to the derived
  group `D`. It uses the central isogeny `Z × D → G` for clause 3. It finds each minimal
  non-central normal subgroup of `G` through its derived subgroup for clause 1. For
  clause 2 it composes `1 × (∏ G′_i → D)` with `Z × D → G`.

## Source

Brian Conrad, *Reductive group schemes* (2014), registered as
`conrad-2014-reductive-group-schemes`: Exercise 5.5.2, printed p.182, and
Theorem 5.1.19, printed p.150.
