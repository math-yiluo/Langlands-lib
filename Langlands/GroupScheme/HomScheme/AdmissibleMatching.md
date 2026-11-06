# Matching actual admissible families

Author: Worker 1726.

This internal helper transfers membership between actual admissible subgroup
families when their restrictions to a common parameter scheme are equal.
It constructs the common original group-valued point over the identity test of
that parameter scheme. The actual restriction membership criterion then gives
membership in both local families. The construction uses arbitrary schemes
and arbitrary relative tests.

`isAdmissible_comapIso` transports a chosen actual closed torus representative
through an isomorphism of ambient group schemes. The range of the composite
inclusion is the inverse-image subgroup, so it remains admissible.

For an open cover of a parameter scheme `T`, `coverSubgroup` regards each
admissible family as a subgroup of the iterated ambient pullback. Its definition
uses the actual direct/iterated pullback comparison. `IsMatchingAdmissible`
requires equality after restricting along any two maps from a common parameter
scheme that agree over `T`.

`isMatching_coverSubgroup` derives the all-test matching condition of
`SubgroupFunctor.ZariskiDescent` from this ordinary matching condition. Given a
comparison between two relative tests, its structure maps supply a common
parameter scheme. Naturality of the pullback point equivalence and the
projection identities of the ambient comparison show that the two transported
points have the same projection to the original group. The first membership
transfer lemma then applies.

These are internal categorical constructions derived from actual family
restriction, pullback point equivalences and subgroup ranges. They do not
assume a representing moduli scheme. Effective closed representability of the
descended subgroup and moduli sheafness remain subsequent steps.
