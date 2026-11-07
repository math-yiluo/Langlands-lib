# Continuous characters on a compact quotient

Let `A` be a commutative topological group and `D` a subgroup. The quotient has
its usual quotient topology. `descend` sends a continuous circle-valued
character trivial on `D` to the induced character of `A / D`. The quotient-map
criterion proves continuity. `descendHom` applies this construction to a subgroup
`H` of characters, all trivial on `D`, preserving multiplication.

Assume the quotient is compact Hausdorff. If the characters in `H` detect every
element outside `D`, their descended characters separate any two quotient
points: apply the hypothesis to the ratio of representatives. The
compact-character completeness argument then says that the range of
`descendHom` is the entire continuous dual of the quotient.

Every continuous character of `A` trivial on `D` therefore descends to a
character in that range. Equality after descent implies equality on `A` by
evaluation at quotient classes. This proves `mem_of_separates_quotient`.

This is an internal supporting construction for adelic additive duality.
It adapts the quotient-character step of Worker 1843's proposed abstract
argument using `CompactCharacterCompleteness`. It does not prove the
arithmetic separation hypothesis or provide a parametrization of characters
that are nontrivial on `D`.
