# Closed support of a scheme module

For any scheme `X` in universe `u` and any actual module sheaf `M`,
`closedStalkSupport M` is the topological closure of `stalkSupport M`,
regarded as a closed subset of `X`. The existing stalk support consists
of points where the underlying abelian stalk is nonzero. Taking its
closure does not assume that the stalk support itself is closed.

Containment in a closed set `Z` is equivalent to vanishing on its open
complement. One direction excludes the open from stalk support and uses
the published stalk criterion for vanishing; the other uses the
published implication from local vanishing to support containment and
the minimality of closure. In particular, a module vanishes outside its
own closed support. This closed support is empty exactly when the
module is zero, and isomorphisms preserve it.

The existing `HasSupportDimensionLT M e` predicate is equivalent to
requiring that every ambient irreducible closed subset of
`closedStalkSupport M` have height less than the natural number `e`.
Indeed, the closed support is the least possible witness for the
existing predicate. `ClosedSupportTopology.topologicalKrullDim_lt_iff`
then gives the equivalent inequality
`topologicalKrullDim (closedStalkSupport M) < e`. This includes the
empty support and `e = 0`, using the existing `WithBot ENat` convention.

For an actual short exact sequence, exactness of the forgetful functor
to abelian sheaves and of the stalk functor gives a short exact sequence
of abelian stalks. Its middle object is zero if and only if both outer
objects are zero: exactness gives one implication, and monicity and
epimorphy give the other. Hence the middle stalk support is the union of
the outer supports. Closure commutes with a binary union, giving the
same union formula for closed supports.

This is an internal definition and its derived comparison lemmas, built
from the published actual support and local vanishing interfaces.
Neither coherence nor Noetherianness is needed. The module makes no
Euler-polynomial or positivity assertion.
