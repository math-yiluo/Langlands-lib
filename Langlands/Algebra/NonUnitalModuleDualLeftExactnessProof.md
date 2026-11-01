# Actual left-to-right dual exactness: categorical bridges

This internal proof module supplies the left-to-right part of the categorical
exactness target for Renard I.4.1, printed pp.22–23 / PDF pp.28–29. It uses the
published actual dual functor and the named abelian structures on the original
nondegenerate module categories. The inherited Hom addition is pointwise.

The additivity proof is precisely the published additivity of actual pullback.
The published concrete categorical exactness criterion identifies the middle
kernel with the range of the first original intertwiner; the zero composite
provides the converse inclusion. The resulting `Function.Exact` statement is
reversed by `pullback_exact` from `NonUnitalModuleDualMapExactnessProof`, and the
same concrete criterion returns categorical exactness of the reversed complex.
Similarly, the published mono/injectivity and epi/surjectivity criteria together
with the two endpoint pullback theorems prove reversal of each boundary map.
Combining them gives reversal of every short exact complex.

For each of Renard's one-sided conditions, a complex in the opposite category
is unopposed. Its exactness unopposes, and its mono or epi boundary becomes,
respectively, an epi or mono in the original category. The preceding results
then establish the required exactness and boundary condition.

These are internal derived proof steps for the unchanged categorical statement,
not new assumptions or a replacement duality. They inherit the unrestricted
dimension, original nonunital action and recovered complex scalars of the map
proof. That proof uses full-dual extension and idempotent projection instead of
Renard's fixed-part identification. No fixed-part inverse, equivalence,
naturality or bidual theorem is used here. The accompanying final categorical
proof describes the right-module orientation and the source provenance.
