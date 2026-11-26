# Leading and tail columns of the lower rectangle in the real gap kernel

This module is the real counterpart of the Library's `ComplexGapSplitTestColumns`. Notation as in
`RealTwoBlockHaar` and `RealGapTailMatrix` with the block sizes `t + 1` and `r − t`.

* `leadingColumns hkn g` is the `(r+1) × (t+1)` matrix of the first-block columns of
  `g ∈ GL_{r+1}(ℝ)`, in the block indexing `tailBlockIndex`; `tailColumns hkn g` (from
  `RealGapTailMatrix`) are the remaining columns.

`RealGapSplitTestColumnsStatement` (proved by `realGapSplitTestColumns`): for `t < r`,
`B ∈ GL_{r+1}(ℝ)`, `z ∈ GL_{t+1}(ℝ)` and an `(r−t) × (t+1)` matrix `Y`, the matrix
`C = B · diag(z, 1) · lowerRectangle h Y` satisfies

`leadingColumns C = B · leadingInput z Y` and `tailColumns C = tailColumns B`,

where `leadingInput z Y` stacks `z` above `Y` (`RealGapOrdinaryMajorant`).

The proof writes `diag(z, 1) · lowerRectangle h Y` as the reindexed lower block matrix
`[[z, 0], [Y, 1]]` (`realTwoBlockEntries` and the lower-block multiplication rule). Its first-block
columns are the stack of `z` and `Y` and its other columns are those of the identity. Multiplying by
`B` gives the two identities. They identify the arguments of the Schwartz tests in the two-block kernel
of `RealGodementTwoBlockRestriction` at `b = lowerRectangle h Y` with those bounded by
`RealGapOrdinaryMajorant`.
