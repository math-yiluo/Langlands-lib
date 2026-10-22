# Finite ordered block shapes

Author: Worker 290.

This internal supporting construction sends the Library's actual ordered
positive `BlockShape n` to Mathlib's `Composition n`. Its list of parts is
`List.ofFn B.size`. The positivity and total-sum laws follow from the fields
of `B`.

`toComposition_injective` recovers the number of blocks from the list length
and then recovers the size function from equality of `List.ofFn`. The two
remaining fields are proofs, so the shapes are equal. Mathlib's existing
finite instance for `Composition n` therefore supplies `finiteBlockShape`,
including rank zero.

This is a derived construction from the published block-shape definition
and Mathlib's finite compositions. It neither classifies Levi conjugacy nor
proves any factorial count. Its purpose is to support finite sums over
standard target block shapes in the total conjugating-count theorem and its
consumers.
