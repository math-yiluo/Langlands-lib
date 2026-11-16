# Compact neighborhoods invariant under a compact right factor

Author: Worker 306.

This is internal topological support for
`Langlands.Analysis.Local.RightInvariantFactorizationIntegral`.
It defines `rightFactorThickening K U` to be the pointwise product `U K`
of a set and a subgroup in a group.

The supporting lemmas prove that `U ⊆ U K`, that `U K` is invariant under
right multiplication by `K`, and that the product is compact when both
factors are compact. If `U` is a neighborhood of one, so is `U K`.
Consequently, in a locally compact topological group, every compact
subgroup `K` has a compact
neighborhood of one with this right invariance. The construction chooses
an arbitrary compact neighborhood `U` and takes its product with `K`.
No positivity assertion about the ambient measure of `K` is needed.

The final lemma concerns a closed subgroup `P` of a Hausdorff
topological group and a compact neighborhood `C` of one. For any Borel
measure `ρ` on `P` that is positive on nonempty open sets and finite on
compact sets, it proves

```text
0 < ρ {p : P | (p : G)⁻¹ ∈ C} < ∞.
```

Continuity pulls the neighborhood back to a neighborhood of one in `P`,
so its measure is positive. The map that includes `P` in `G` and then
inverts is a closed embedding, so the same inverse image is compact and
has finite measure. Every Haar measure has the two required measure
properties.

All results are derived from elementary subgroup algebra, local
compactness, and the stated measure properties. They do not provide an
Iwasawa decomposition, a quotient integral formula, or a Mellin estimate.
