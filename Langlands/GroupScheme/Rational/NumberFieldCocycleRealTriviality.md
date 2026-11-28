# Local triviality of finite field cocycles from the real places

`Cocycle.RealLocallyTrivial` asks for a trivialization on the full pullback
cover at each real place. It is preserved by coefficient homomorphisms.

For a simply connected group, compare the cocycle to the coboundary of the
unit cochain. At a real place both cocycles have primitives, and the ratio
of the primitives gives a cohomology comparison. The published
`simplyConnectedRealToAllPlacesComparison` supplies the comparison at every
completion. The unit coboundary is trivial at every completion, so the
original cocycle is also locally trivial there.
