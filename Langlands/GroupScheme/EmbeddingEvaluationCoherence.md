# Pullback evaluation components and canonical descent

Worker 166. This is an internal consequence of the universal property of
actual scheme pullbacks and the published direct/iterated base-change and
canonical descent comparisons. No external structural assertion is introduced.
All schemes are in an arbitrary universe `u`.

Let `b : S → B`, `l : T → B` and `t : T → S` satisfy `t ≫ b = l`,
and let `W` be a group scheme over `B`. The map
`EmbeddingProduct.intermediateProjection b l t ht W` from `W_l` to `W_b`
is the actual pullback lift. Its projection to `W` is the original first
projection, and its projection to `S` is the projection to `T` followed by `t`.
`pullbackComparison_inv_intermediateProjection` identifies this map with the
inverse direct/iterated comparison followed by the intermediate projection.
The proof tests the two pullback projections.

For a group scheme `H` over `S` and any homomorphism `e : W_b → H`,
`evaluationComponent b l t ht W H e` is the inverse direct/iterated
comparison followed by the actual base change of `e` along `t`.
`evaluationComponent_fst` identifies its underlying projection to `H` as
`intermediateProjection ≫ e`. There are no affineness or field hypotheses.

Suppose further that `a : T → T` satisfies `a ≫ l = l`, and `t' : T → S`
satisfies `t' ≫ b = l` and `a ≫ t = t'`. Then
`intermediateProjection_descent` proves that canonical descent on `W_l`
followed by the `t'` intermediate projection equals the first projection from
the `a` pullback followed by the `t` intermediate projection. Both pullback
projections prove this equality. Finally, `evaluationComponent_descent` states
that base change along `a` of the `t` component followed by the direct/iterated
comparison equals canonical descent followed by the `t'` component. The proof
again tests pullback projections, using the intermediate projection identity
for the projection to `H` and the over-category structure for the base.

This module proves coherence for a supplied evaluation map. It does not identify
any particular Weil-product coordinate or prove the host structural theorem.
