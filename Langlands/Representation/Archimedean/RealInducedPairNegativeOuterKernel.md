# An exact reversed-source presentation of the outer replacement kernel

This internal derived unit turns the pulled-back inner-binomial kernel of
`RealInducedPairNegativeOuterQuotient` into the range of an actual exact
intertwiner from a mixed standard module.

For every linked `d,e,k` with negative signed inner weight, retain the notation
`u,v,x,y`, `h`, and `rawOuter` of the negative-inner constructions. The existing
outer source is `[character x,induced rawOuter,character v]`. Define
`companionSource` by reversing these two remaining character blocks:
`[character v,induced rawOuter,character x]`. Their actual character parities
are retained.

`RealInducedPairNegativeOuterKernelStatement` asserts that there is a complex-
linear exact intertwiner from this companion source to the existing outer
source whose range is exactly the kernel of the existing actual replacement
quotient. `realInducedPairNegativeOuterKernel` proves this proposition for all
linked negative-inner data, without an outer-square or additional parity
hypothesis.

The character `v` is interlaced in the outer block at distance `L` from its
lower endpoint, with `0<L<P`. The published interlaced equivalence extended
through the final character `x` gives `companionEquiv` to the actual list
`[induced rawOuter,character v,character x]`.

The existing `exposeEquiv` takes the original outer source to
`[induced rawOuter,character x,character v]`. The inner pair here is ascending
with positive gap `h` and the proved reducible parity. Apply its exact
binomial map from the exposed companion list, then undo `exposeEquiv`.
This defines `kernelGenerator`. Each reordering is an exact equivalence, and
the middle binomial is an exact rank-one intertwiner with the outer induction
block retained. Their composite is exact.

The existing replacement-quotient kernel is the inner-binomial range pulled
back through `exposeEquiv`. Surjectivity of `companionEquiv` and injectivity
of `exposeEquiv` therefore give `range_kernelGenerator` in both directions.
The replacement quotient composed with this generator is zero.

This is a source-level kernel presentation. It does not prove that the
mixed-source filtration map sends this kernel into the earlier swapped-pair
range and does not identify either full crossing composite. When comparing
positive and negative crossed pairs, the actual endpoint parities must be
checked separately; exponent reversal alone is insufficient. The unrestricted
two-induction-block filtration remains open.
