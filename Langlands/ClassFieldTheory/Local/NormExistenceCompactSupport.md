# Compactness in the norm-subgroup existence argument

This is generic supporting work for the local norm-subgroup existence theorem.
It does not assert that any particular arithmetic family satisfies its
hypotheses.

For a commutative topological group, the first theorem takes a nonempty
downward directed family of closed subgroups, a compact subgroup `U`, and an
open subgroup `H` containing the intersection of the family. It finds a member
`N` with `N ∩ U ≤ H`. The proof applies compactness to `U \ H` and the
directed family of closed subgroup carriers.

The second theorem proves `N ∩ (U ∨ (N ∩ H)) ≤ H` from `N ∩ U ≤ H`.
Write an element of the join as a product of an element of `U` and an
element of `N ∩ H`; membership of the product in `N` puts the first factor
in `N ∩ U`.

The third theorem assumes the family is closed under intersections and
finite-index overgroups, all its members are closed and of finite index, and
every open finite-index overgroup of `U` belongs to the family. It proves that
any open finite-index subgroup containing the universal intersection belongs
to the family. After the first theorem selects `N`, the subgroup
`U ∨ (N ∩ H)` is open and of finite index. Intersecting it with `N` and
using the second theorem gives a family member contained in `H`; upward
closure finishes.

The argument is the topological part of Serre, *Local Fields* (1979),
Chapter XI, §5, Theorem 2, printed pages 174–175 (PDF pages 180–181).
This implementation isolates that argument from the arithmetic statements
about universal norms, proper norm maps, and unramified extensions. The
subgroup identity is an internal elementary step in the same proof.

The Prop-valued declaration `CompactNormSubgroupCriterion` packages the complete assertion above. Its lowercase theorem proves the assertion using the preceding supporting lemmas. The entry assertion and these proofs are supplied together for review.
