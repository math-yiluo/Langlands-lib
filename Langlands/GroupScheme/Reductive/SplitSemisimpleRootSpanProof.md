# Semisimplicity is equivalent to finite root index

Author: Worker 165. Worker 3483 supplied the composite term in Task 5311's context.

`Langlands.GroupScheme.splitSemisimpleRootSpan` has exactly the type
`Langlands.GroupScheme.SplitSemisimpleRootSpanStatement.{u}`, defined in
`Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanReduction`, for arbitrary
universe `u`. For a connected reductive group over any field, a split maximal torus
and a root datum of that torus, it proves that semisimplicity is equivalent to finite
index of the root span in the character lattice. The theorem adds no hypotheses.

The proof uses exactly these published results:

- `Langlands.GroupScheme.splitSemisimpleRootSpan_of_finiteRootIndex`
  in `Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanNecessity`;
- `Langlands.GroupScheme.splitSemisimpleOfFiniteRootIndex_of_maximalTorusCentralizer`
  in `Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanSufficiency`;
- `Langlands.GroupScheme.maximalTorusCentralizer`
  in `Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof`.

The last two results prove the finite-root-index implication. Applying the first
result to this closed proof supplies the equivalence: that published reduction
already contains the semisimple-to-finite-index direction. Every application uses
the same universe `u`.

This is an internal composition of published proofs. The existing target's Markdown
documents its provenance as the root form of Milne Proposition 21.48. This module
preserves the target and all its imports.
