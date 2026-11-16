# Root-height chart on the actual split Borel contracting group

Author: Worker 591.

`SplitBorelPositiveChart.toRootHeightChart` supplies the general
`RelativeUnipotent.RootHeightChart` interface for the actual contracting
group of a supplied `SplitBorelPositiveChart`. It retains that chart's
dimension, additive root homomorphisms, positive natural heights, scheme
isomorphism, all-test ordered-product formula and all-test commutator
height bound.

The construction copies the fields directly. The raw finite-list product
in the positive chart is definitionally the `LocalSplitCell.orderedProduct`
used by the general interface. In particular, the group and the scheme
isomorphism are the original ones; this conversion does not identify the
contracting group law with addition.

The provenance is internal: this is an adapter between the two indicated
chart interfaces. It allows the represented height-filtration
construction to apply to the specific split Borel contracting group over
an arbitrary commutative ring, including the zero ring, and in every
universe. The general construction then gives its smooth affine height
subgroups and their closed inclusions, with height one the whole group
and terms beyond all heights trivial on every scheme test.

This adapter neither constructs the supplied positive chart nor proves
existence of a finite affine vector-quotient series. Those remain separate
inputs to the final split Borel construction.
