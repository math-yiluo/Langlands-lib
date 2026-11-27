# Lower Levi coordinates for nonzero-weight real blocks

`discreteSlots` keeps the nonzero-weight induced slots in their list order.
For the monotone labels `blockStart`, a strictly lower entry within one
class has row one greater than its column. The equality of the two labels
then identifies its nonzero-weight slot. Conversely, each such slot
supplies one within-class entry. Distinct slots are disjoint, so this
correspondence is the equivalence `entryEquiv`.

`RealDiscreteLeviEntriesStatement` identifies the actual lower Levi
matrix `lowerMGL` with the product `lowerBlockProduct` of the lower
simple-root elements under this coordinate equivalence. Products of the
off-diagonal matrix units from distinct slots vanish. The product of the
simple-root matrices is therefore the identity plus the sum of the
within-class entries, which is the lower Levi matrix.

`entriesBySlot` reindexes product Lebesgue measure by `entryEquiv`.
`realDiscreteLeviEntryBound` uses this reindexing and the matrix equality
to apply `realDiscreteLeviInnerBound` in the lower Levi chart. The
integral has one independent real frequency per slot and an arbitrary
orthogonal final argument. Its norm is bounded by a constant times the
compact supremum bound and the product of the absolute frequencies to
half the corresponding absolute weights.
