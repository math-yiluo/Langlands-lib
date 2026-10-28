# Replacement at an actual adjacent slot

Author: Worker 494.

This internal construction starts with actual segment-product data `d`, adjacent
positions `j` and `j+1`, and arbitrary supplied inner data `e₂` whose rank is the
size of the merged position. The family `adjacentReplacementDatum` uses `e₂` at
that position and the actual original adjacent refinement at every other position.
`replaceAdjacentSlot` concatenates this family over the same merged outer shape.

The complete block list consists of the original prefix of length `j`, followed
by the complete block list of `e₂`, followed by the original suffix after
position `j+1`. The segment list has the corresponding formula. A finite-list
lemma proves the formula by identifying the unchanged fibers as singletons and
splitting the outer list before and after the merged position. In particular,
all original occurrences and their supplied actual blocks outside the pair are
retained. Strong segment socles are inherited from `d` and `e₂`.

`replaceAdjacentSlotInducedEquiv` specializes the closed concatenation
equivalence. Its source is the actual normalized product over the common merged
outer shape of the replacement inner products; its target is the actual flat
product of the replacement datum. The family is exactly the original inner
family outside the merged position and exactly `e₂` at that position.

The provenance is internal finite-list bookkeeping and specialization of the
actual adjacent refinement and concatenation constructions. The new inner data
are arbitrary of the required rank. No twist freeness, union/intersection
semantics, segment-structure theorem or classification conclusion is used.
The prime and supplied topology are arbitrary, and the field and carrier
universes are independent. The required adjacent pair bound entails at least
two original blocks, so this construction makes no assertion for empty data.
