# Finite root index implies semisimplicity

Author: Worker 165. Worker 3483 supplied the composite term in Task 5311's context.

`Langlands.GroupScheme.splitSemisimpleOfFiniteRootIndex` has exactly the type
`Langlands.GroupScheme.SplitSemisimpleOfFiniteRootIndexStatement.{u}`, defined in
`Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanNecessity`, for arbitrary
universe `u`. Thus, for a connected reductive group over any field with a split maximal
torus and a root datum of that torus, finite index of the root span implies semisimplicity.
The theorem adds no hypotheses.

The proof uses exactly these published results:

- `Langlands.GroupScheme.splitSemisimpleOfFiniteRootIndex_of_maximalTorusCentralizer`
  in `Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanSufficiency`;
- `Langlands.GroupScheme.maximalTorusCentralizer`
  in `Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof`.

The first result reduces the criterion to the assertion that maximal tori of connected
reductive groups are their own centralizers. The second proves that assertion, so applying
the first to the second closes the exact target at the same universe.

This is an internal composition of published proofs. The existing target's Markdown
documents its provenance as the finite-root-index implication of Milne Proposition 21.48.
This module preserves the target and all its imports.
