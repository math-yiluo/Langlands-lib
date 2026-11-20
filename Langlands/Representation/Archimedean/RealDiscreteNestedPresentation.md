# A nested principal-series presentation for tied discrete blocks

The declarations in `Langlands.Archimedean.RealDiscreteNestedPresentation` give a principal-series surjection onto a real standard module with tied discrete-series
blocks, within arbitrary surrounding blocks. For absolute weight ℓ, the signs of the
low and high endpoint characters are respectively `⌊ℓ/2⌋` and `⌊ℓ/2⌋ + ℓ + 1` modulo two.
Their sum meets the tail-map parity requirement.

The donor list puts the low endpoints in increasing order of absolute weight and the
high endpoints in the opposite order. At each stage the adjacent pair of largest
weight maps onto its induction block by `RealInducedCharacter.tail_surjective`.
The resulting block moves right past the remaining high endpoints. Their distances
in real exponent from the tied center are at most half the weight of that block,
so they are unlinked. The corresponding swaps are inverses of the bijective unlinked
swaps going in the other direction. The procedure gives a surjection onto the list
of induction blocks in increasing order of absolute weight.

`nestedChars_perm_splitChars` identifies the donor list as a permutation of the
adjacent high/low pairs in increasing block-weight order, with each sign preserved.
The surjection is derived from the adjacent tail and swap maps.
