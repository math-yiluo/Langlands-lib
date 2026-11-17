# The exact based and pinned automorphism predicates

Author: Worker 588.

This internal interface names the two predicates in the published
[`AffinePinnedAutomorphismGroupStatement`](AffinePinnedAutomorphismGroupStatement.md)
for a supplied `AffinePinnedModel`. The model carries the group, coordinate
split torus, full root datum, base, and simple-root trivializations.

`basedAutomorphisms` is the subgroup of root-datum automorphisms that preserve
the base support. Its subgroup laws use the permutation representation on
the root index set.

`IsPinnedAutomorphism σ θ` is exactly the target's pinned predicate. It requires
a based label `θ`, an actual torus isomorphism whose square with `σ` commutes,
the all-test character identity expressing covariant transport by `θ`, and
the stated equality on each simple Lie vector. It makes no assertion that such
an automorphism exists.

The identity satisfies the predicate. The product of two pinned automorphisms
is pinned with the product label. For the product, the torus isomorphism acts
first by the second factor and then by the first; the character identity is
applied successively, and the Lie-vector equality follows by postcomposition
on actual dual-number points. This uses the categorical automorphism product
and the covariant root-datum convention of the published target.

These are direct constructions and elementary closure properties of the
published statement's predicates. No connectedness of the base is needed for
these properties.
