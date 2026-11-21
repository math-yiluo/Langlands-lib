# Unitary restriction of the actual translation

This is an internal restriction of the coefficient constructions for
Waldspurger V.3 formula (1). It connects the full-character generic tensor
in `ActualParabolicTranslation` to the actual unitary coefficient fibers
in `ActualCommonLeviCoherence`. It uses the source and target parabolics
with their corresponding literal Levi anchors and the transported compact
Iwasawa data.

`unitaryParameter_conjugation` applies the published equality for
restriction of characters after forgetting norm-one membership to the
isomorphism of the represented Levi schemes. The induced equality identifies
the full parameter of a transported unitary point with the transport of its
full parameter. `unitaryTwistEquiv` and `unitaryTranslation` apply that
parameter equality to the published conjugate twist comparison and to the
actual translated coefficient equivalence. Both use the entire unitary
parameter group.

`ofCommonLevi` precomposes a displayed target-side common-Levi comparison
by this precise left translation at each unitary parameter. The resulting
maps intertwine the whole external product action on the actual coefficient
fibers. The continuation and regularity of the target-side common-Levi
family are properties to impose through its existing actual-germ
specification when using this adapter for a normalized family.
