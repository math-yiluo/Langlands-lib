# Integral units in the split valuation kernel

The split similitudes have an opposite-algebra unit and a multiplier
as their two coordinates. For nonarchimedean local fields `F` and `k`,
with `B` a finite-dimensional central division algebra over `F` and
a `k`-algebra, `splitIntegerUnits` is the inverse image of the product
of the two integer-ring unit subgroups. The first uses the integer
ring of `B` and the opposite-unit equivalence. The second is the
integer-ring unit subgroup of `k`. These are the actual unit subgroups
used for the published maximal compact levels.

`localSplitValuationCoordinates_ker` identifies this subgroup with the
kernel of the two actual local orders. A unit has valuation one exactly
when the unit and its inverse both have valuation at most one. The
proof transports the latter bounds through the published comparison
of the integer rings and the valuation of the local scalar field.

This identifies the kernel used by `HarrisComponentQuotient` in
terms of the actual integral unit subgroups. It is an internal
comparison of the Library constructions. The comparison with
the intersection of all rational-character kernels of Harris (A.2)
also needs the rational-character maps.
