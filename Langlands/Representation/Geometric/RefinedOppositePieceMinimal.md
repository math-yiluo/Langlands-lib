# Minimality of the reversed whole-piece coordinate

This internal combinatorial derivation concerns the actual permutation
`reversedPiecePermutation B S C x` constructed in
`RefinedOppositePieceTransport`. It proves that the permutation is minimal
from the coarse source `B` to `C.reverse` when `x` is minimal from `B` to
`C` and conjugates the actual Levi of `B.flatten S` onto the Levi of `C`.
The result is independent of any representation or geometric lemma.
The definition `reversedPieceMinimalRepresentative` packages this exact
permutation and its proved minimality as an element of
`MinimalRepresentatives B C.reverse`, the actual index type of the upper
geometric filtration. Its permutation is fixed by the input data.

The block-label identities for reversal follow directly from the
constructed reversal permutation on standard block coordinates. Inner
reversal preserves coordinate order within each fine block, in both
directions. The published flattened pair criterion therefore proves its
minimality between the reversed and original flattened shapes.

Refining the source of a minimal representative preserves minimality:
each fine source block is contained in a coarse source block. Composing
this fine minimal permutation with inner reversal and then inverse outer
reversal proves fine-source minimality. The proof uses the published
composition criterion and the block-partition equality supplied by actual
Levi conjugacy.

To recover coarse-source minimality, the proof checks target block
labels. Equal source inner labels have equal target labels by actual
conjugacy. Strictly increasing inner labels imply increasing source
coordinates and hence increasing target coordinates by coarse
minimality. Inner reversal reverses the inner labels, and inverse target
reversal reverses the target labels, so their composite has monotone
target labels on each coarse block. The already established increasing
inverse on target blocks then gives increasing values on each coarse
source block, using the published `lt_of_blockIndex_le`.

This is derived infrastructure with no external literature assertion.
It supplies an actual minimal filtration index but does not construct a
filtration, compare its grades, prove subquotient occurrence, select a
noncoarse branch, or establish continuation or the host obstruction.
