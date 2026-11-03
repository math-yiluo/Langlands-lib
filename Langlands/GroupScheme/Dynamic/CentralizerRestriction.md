# Restriction of dynamic centralizers to closed subgroups

Author: Worker 1438.

This internal construction supports the proof of
`CentralizerBorelIntersectionStatement`. It is derived directly from the
published definitions, rather than asserting a new structural theorem from the
literature. It works over any base scheme, with arbitrary cocharacters and all
test schemes, including non-affine and nonreduced tests.

The construction `Dynamic.restrictCocharacter` factors an ambient cocharacter
through a monic subgroup whose range contains its range. It applies the
published `SubgroupFunctor.IsRepresentedBy.factorHom` to the subgroup's own
range; `Dynamic.restrictCocharacter_comp` verifies the factorization equation.
In particular no injectivity or nontriviality assumption on the cocharacter is
needed.

For a monomorphism `b : H ⟶ G` and cocharacter `χ : Gm ⟶ H`, the theorem
`Dynamic.mem_centralizer_comp_iff` says that a point of `H` centralizes `χ`
if and only if its image centralizes `χ ≫ b`. The implemented proof uses the
published identification of dynamic centralizers with universal commutation.
It postcomposes the commutation equation and cancels the monomorphism in the
reverse direction.

If `j : M ⟶ G` represents the ambient centralizer, the actual pullback
`subgroupIntersection j b`, mapped to `H` by its second projection, has range
exactly the internal centralizer of `χ`. The forward implication uses the
pullback equation and the preceding cancellation lemma. The reverse
implication lifts a pair of points by the actual pullback universal property.
For closed `j` the second projection is closed by base change. For closed `b`
and `j`, these results establish `IsRepresentedBy` for that projection.

Finally, for any representative `c : C ⟶ H` of the internal centralizer,
`Dynamic.range_internalCentralizer_comp` identifies its composite range in
`G` with the intersection of the ranges of `j` and `b`. This is an equality
of subgroup functors on every test scheme, rather than an assertion only on
rational points.

No smoothness, connectedness, solvability, or Borel maximality is concluded.
To use this construction for the main target, one must still prove that a
Borel of the ambient centralizer lies in the chosen ambient Borel. In
particular this module supplies no proof of Milne 2017, Theorem 17.46.
