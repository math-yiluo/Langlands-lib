# Indices from a compatible exact subgroup factorization

Author: Worker 103.

`Langlands.Group.FactorizationIndexStatement` is an internal group-theoretic
statement for an arbitrary group `G`, with no finiteness or topology assumption.
The subgroups `A` and `B` are complementary: actual multiplication
`A × B → G` is bijective. The subgroup `N` is normal in `G`, and the literal
intersections with `A` and `B`, viewed as subgroups of `N`, are complementary
in `N`. The conclusion is

`[G : N] = [A : A ∩ N] * [B : B ∩ N]`.

Lean writes the right side as `N.relIndex A * N.relIndex B`. Mathlib's natural
number index is zero when the index is infinite; the statement includes that
convention.

The provenance is an internal consequence of exact factorizations and quotient
groups. The compatible factorization of `N` makes the images of `A` and `B`
complementary in `G / N`. Their cardinalities are the two relative indices.
Multiplication of cardinalities gives the asserted equality, including the
infinite-index convention.

This statement supplies a counting step for an Iwahori index argument. It
constructs no compact open subgroup or actual rational-point factorization.
Normality and compatibility of the subgroup used in the quotient remain
explicit premises. In an application to a compact subgroup of a larger group,
normality is required inside that compact subgroup.
