# Unconditional Steinberg tensor embeddings

Author: Worker 165. Worker 3483 supplied the composite term in Task 5311's context.

`Langlands.GroupScheme.steinbergTensorEmbedding` has exactly the type
`Langlands.GroupScheme.SteinbergTensorEmbeddingStatement.{u}`, defined in
`Langlands.GroupScheme.Reductive.SteinbergTensorEmbeddingStatement`, for arbitrary
universe `u`. For every simply connected group over an algebraically closed field of
prime characteristic, with the target's existing affine-total-space instance, it gives
the specified diagonalizable subgroup and tensor embeddings of finite stable invariant
coordinate spaces. The theorem adds no hypotheses.

The proof uses exactly these published theorems:

- `Langlands.GroupScheme.steinbergTensorEmbedding_of_covariantExhaustion`
  in `Langlands.GroupScheme.Reductive.SteinbergCovariantReduction`;
- `Langlands.GroupScheme.steinbergCovariantExhaustion_of_bigCell`
  in `Langlands.GroupScheme.Reductive.SteinbergBigCellReduction`;
- `Langlands.GroupScheme.steinbergBigCell_of_rootAndCoroot`
  in `Langlands.GroupScheme.Reductive.SteinbergBigCellRootCorootAssembly`;
- `Langlands.GroupScheme.rootDatumExistence`
  in `Langlands.GroupScheme.Reductive.RootDatumExistence`;
- `Langlands.GroupScheme.splitSimplyConnectedCorootSpan`
  in `Langlands.GroupScheme.SimplyConnected.SplitNecessity`.

Root-datum existence and the simply connected coroot-span theorem discharge the
two inputs of the big-cell assembly. Applying the covariant-exhaustion reduction
to those data closes `SteinbergCovariantExhaustionStatement.{u}`. The final
published reduction turns this exhaustion into the tensor embeddings: two
representations of the same finite size, a rationally irreducible first factor,
and an injective intertwiner on every test algebra. All applications use the same
universe `u`.

This is an internal composition of published proofs. The target's Markdown explains
the interface's reconstruction from the Haboush proof sketch and its precise scope.
This module preserves that statement and its imports.
