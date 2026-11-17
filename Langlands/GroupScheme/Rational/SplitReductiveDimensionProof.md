# The dimension of a split reductive group

Worker 569.

`Langlands.GroupScheme.splitReductiveDimension.{u}` proves the unchanged
published proposition `Langlands.GroupScheme.SplitReductiveDimensionStatement.{u}`.
For every field `k : Type u`, every connected reductive group scheme `G`
over `Spec k`, and every split maximal torus `t : T.toGrp ⟶ G`, it states

```text
topologicalKrullDim G.X.left =
  topologicalKrullDim T.toGrp.X.left + ((relativeRoots t).ncard : WithBot ℕ∞).
```

The theorem has no additional hypotheses. It imports the published statement
without changing that statement or its dependencies.

## Implemented proof

The private dimension bridge applies the published
`Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension` to a smooth
connected affine group scheme. This supplies a natural number `n` and
`SmoothOfRelativeDimension n` for its structure map. The published
`ReducedBaseSmooth.topologicalKrullDim_eq_of_smoothOfRelativeDimension`
identifies its topological Krull dimension with `n`.
`Lie.dimension_eq_of_smoothOfRelativeDimension` identifies its actual
dual-number Lie dimension with the same `n`. Consequently its topological
dimension equals its Lie finrank, as an element of `WithBot ℕ∞`.

For the supplied split maximal torus, `rootDatumExistence` supplies a finite
index type `J` and an actual root datum `P`. The published
`IsRootDatumOf.finrank_lie_eq_torus_add_card` gives
`finrank Lie(G) = finrank Lie(T) + Nat.card J`. Its proof uses the internal
adjoint weight decomposition, maximal-torus self-centralization for the
zero weight, and the published split root Lie-line theorem for each nonzero
root weight.

The equality `Set.range P.root = roots t` in `IsRootDatumOf` and injectivity
of `P.root` identify `Nat.card J` with `(relativeRoots t).ncard` by
`Set.ncard_range_of_injective`. The private dimension bridge applies to
both `G` and `T`; casting the Lie dimension formula gives the required
equation. This includes the case of an empty root set.

## Provenance

This is a proof of James S. Milne, *Algebraic Groups* (2017),
Corollary 21.13, printed p.430 (PDF page 446), using the already published
Library results named above. The registered source is
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The corollary and its proof were read in that source.

The implemented route follows Milne's Lie weight counting argument and
his passage from Lie dimensions to scheme dimensions by smoothness.
It uses the existing finite root datum only to index the actual roots;
no classification assumption is added. The private dimension bridge is
an internal composition of the published constant smooth relative
dimension and Lie/stalk dimension results.

The complete registered official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`,
was read; it contains no correction to Corollary 21.13.
