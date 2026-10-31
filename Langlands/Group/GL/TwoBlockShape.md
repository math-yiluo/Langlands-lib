# The positive two-block shape with a prescribed cut

`Langlands.ProductLeviChamber.twoBlock N k hk hkN`, for natural numbers
`N` and `k` with `0 < k < N`, is the `BlockShape N` with length two and
ordered sizes `![k, N - k]`. Its positivity and size-sum fields follow from
these inequalities.

`twoBlock_index_val` identifies the consecutive-block numbering: coordinate
`r` of the first block has index `r`, and coordinate `r` of the second block
has index `k + r`.

These are the existing constructor and coordinate lemma moved unchanged from
[ProductLeviChamberBoundProof](../../Representation/Classification/ProductLeviChamberBoundProof.md).
Their declaration names, parameters, defining fields and proof bodies are
preserved. They require only the block-shape infrastructure and arithmetic
tactics, without representation or local-field assumptions.

The chamber-bound proof and
[UpperUnipotentCoinvariantReduction](../../Representation/Whittaker/UpperUnipotentCoinvariantReduction.md)
share these declarations. The latter's identical `cutShape` and
`cutShape_index_val` copies have been removed; its remaining helpers use
`twoBlock` and `twoBlock_index_val` directly.
