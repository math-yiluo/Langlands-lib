# A common Borel for normalized connected solvable subgroups

This is an internal derived geometric construction for the positive-support
step of the Levi-centralizer argument. Work over an algebraically closed field
in arbitrary universe `u` and characteristic. Let `G` be affine and locally of
finite type. Let `i : U → G` and `j : T → G` be supplied homomorphisms
with smooth connected solvable sources. Assume the whole subgroup
functor `range i` is normalized by `range j`.

`exists_isBorelSubgroup_containing_normalized_solvable` constructs an actual
Borel embedding `b : B → G` and group-scheme maps from both supplied sources
whose composites with `b` equal `i` and `j`. `CommonBorelData` records these
objects, and `commonBorelOfNormalizedSolvable` chooses them. The construction
does not require the first subgroup to be normal in `G`.

The two rational-point image groups are solvable, and normalization makes
their join solvable. The group helper proves this inside the join, where the
first factor is normal; it then applies the existing normal-join solvability
lemma. The second helper identifies every element of this join with a product
of one point from each factor.

The existing rational-point closure theorem supplies a smooth closed subgroup
`Z` on the closure of this join. Its rational points embed into the closure
group, which remains solvable, so `Z` is solvable. To prove connectedness, take
the union of the image of `U` with every translate of the image of `T` by a
rational point of `U`. Each translated image meets the image of `U`, hence
the union is preconnected. Closed-point density over the algebraically closed
field places this union in the closure of the rational-point join. The product
decomposition gives the reverse containment after closure. The closed subgroup
`Z` is therefore connected. This connectedness argument is adapted from the
published `Absolute/NormalUnipotentBorelContainmentProof`.

Both original sources are smooth, hence reduced. The existing closed-subgroup
factorization theorem upgrades containment of their rational points in `Z`
to actual factor maps. Finally `BorelContaining` places `Z` in a Borel, and
composition gives the two asserted factorizations. Thus the conclusion holds
on every test scheme. Use of rational points in this proof is justified over
the algebraically closed field by the imported reduced-source factorization
theorem; the conclusion is not restricted to rational point sets.

The imported constructions are
`Absolute/RationalPointClosureProof`,
`Absolute/RationalPointClosureSolvable`,
`Absolute/NormalUnipotentBorelContainmentProof`, and
`Absolute/BorelContaining`. This module introduces no new literature assertion.
The specialization
`exists_isBorelPair_containing_normalized_unipotent` treats a supplied maximal
torus and a supplied smooth connected unipotent closed subgroup which it
normalizes. Torus geometry gives smoothness and connectedness, and unipotent
points are solvable. It returns a Borel pair with the original torus morphism
and an actual factor map for the supplied unipotent subgroup.

This first geometric step does not yet produce a cocharacter
strictly positive on its actual weights, prove root reflection existence, or
establish the final ambient maximal split centralizer statement.
