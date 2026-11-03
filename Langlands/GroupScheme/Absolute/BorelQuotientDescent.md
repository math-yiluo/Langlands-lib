# Borel subgroups descend through cartesian quotient squares

This is an internal derived prerequisite for the central quotient branch of the
Borel normalizer argument. It does not assert the existence of quotient group
schemes.

For any base scheme and a commuting group-scheme square, the construction
`quotientOvergroupHom` sends a factorization `BQ → H → Q` of `j` to an actual
homomorphism `B → G ×_Q H`. Its inclusion composite is `i`, and its projection
composite is `B → BQ → H`. This construction is the pullback lift in the
category of group schemes and requires no smoothness or field hypothesis.

Over an algebraically closed field, consider a cartesian square with horizontal
closed subgroup homomorphisms `i : B → G` and `j : BQ → Q`, and vertical maps
`p : B → BQ` and `q : G → Q`. Assume `i` is Borel, `q` is smooth, surjective,
quasi-compact and geometrically connected, and `p` is smooth and surjective.
The theorem `isBorelSubgroup_of_quotient_square` proves that `j` is Borel.

Smoothness descends from `B` along `p`. Connectedness descends by continuity
and surjectivity. The map on rational points is surjective because the base
field is algebraically closed and `p` is locally of finite type. Solvability
therefore descends from `B(k)` to `BQ(k)`, using the published comparison
between solvability of a group scheme and its base rational points.

For maximality, pull back a smooth connected solvable closed overgroup
`H → Q` to `P → G`. This preimage is closed and smooth; geometric
connectedness of `q` ensures that it is connected. The original cartesian
square gives a homomorphism `fB : B → P`. On rational points, the kernel
of `P(k) → H(k)` lies in the image of `B(k)`: the original cartesian square
lifts each such kernel point to `B(k)`, and the closed embedding `P → G`
identifies its image with the original point. Mathlib's solvable extension
criterion then proves that `P(k)` is solvable.

Borel maximality of `i` makes this `quotientOvergroupHom`, denoted `fB`,
an isomorphism. Pullback pasting
identifies `fB` as the pullback of the proposed factor `BQ → H`.
Isomorphisms descend along the fpqc map `P → H`, so the factor is an
isomorphism. Forgetful functors reflect this isomorphism back to group
schemes, proving the required maximality.

The proof uses the published subgroup-preimage and connected-kernel geometry
interfaces, smooth source descent, rational-point lifting, and Mathlib's
fpqc descent of isomorphisms. No additional structural hypothesis is supplied
to the final Borel normalizer statement; this helper retains actual supplied
quotient data as its scope.
