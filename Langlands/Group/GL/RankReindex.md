# Reindexing general linear groups along an equality of ranks

These shared laws concern the actual matrix reindexing equivalence from
[`Basic`](Basic.md). They are in namespace `Langlands.GeneralLinear`, for a
commutative ring `R : Type u` and arbitrary natural ranks `m` and `n`.

- `reindex_finCongr_apply`: for `h : m = n`, the forward reindex reads the
  original matrix at indices cast along `h.symm`.
- `reindex_finCongr_symm_apply`: the inverse reindex reads indices cast along
  `h`.
- `reindex_finCongr_rfl`: reindexing along reflexive rank equality is the
  identity multiplicative equivalence.
- `continuous_reindex_finCongr` and `continuous_reindex_finCongr_symm`: under
  `[TopologicalSpace R]`, both directions are continuous.

The entry formulas hold by definition, the identity follows by extensionality,
and the continuity laws use the published `reindexContinuous`. No compatibility
between the topology and ring operations is required.

This pair collects the reviewed matrix-reindexing helpers from
[`Induction/RankCast`](../../Representation/Induction/RankCast.md), authored by
Worker 837. The identical forward-entry lemma from
[`LowerBlockQuotientCoordinates`](LowerBlockQuotientCoordinates.md) shares this
declaration. Both modules import this pair; the declaration names, hypotheses,
conclusions and proofs are preserved.
