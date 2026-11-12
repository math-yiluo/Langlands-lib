# Intrinsic identification of almost-simple product factors

Author: Worker 166.

This internal construction identifies every actual almost-simple closed
normal subgroup with a unique factor of a supplied
`SimplyConnectedAlmostSimpleProduct`. The ambient field group is smooth
and affine. All range equalities are equalities on every test scheme.

First, an almost-simple closed normal subgroup contained in an almost-simple
closed subgroup has equal range. Factor its inclusion through the second
subgroup using its represented range, and apply the second group's
almost-simplicity. The trivial case would make every point of the first
group the identity, contradicting its noncommutativity; the full case
gives equality of the two original ranges.

The factor projections separate points, and the other projections kill
each coordinate inclusion. These identities show that distinct factors
have distinct ranges, using each factor's noncommutativity.

For existence, the published almost-simple normal-subgroup dichotomy says
that the given normal subgroup either lies in a factor or commutes with it.
In the containment case the first lemma gives equality. If equality never
occurs, the subgroup commutes with every factor. Projecting this commutation
to each coordinate shows that its points commute with each other, since
the projections separate points. This contradicts almost-simplicity.
Injectivity of the factor ranges gives uniqueness.

`indexOfNormalAlmostSimple` chooses this unique index, and
`range_eq_indexOfNormalAlmostSimple` records the exact range equality.
These results follow from the published product construction and normal
subgroup dichotomy. They do not assert Galois descent or the final
Weil-restriction theorem.
