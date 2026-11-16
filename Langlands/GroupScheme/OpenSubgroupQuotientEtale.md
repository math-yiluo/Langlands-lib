# Étaleness of a smooth quotient by an open subgroup

This internal construction supports the smooth-affine torus Weyl quotient.
It uses the published actual right-coset relation of
`HomogeneousCosetRelation`, descent of open immersions along fppf morphisms,
and `smooth_of_smooth_of_surjective_of_smooth_comp`. Its provenance is the
combination of these Library interfaces and their universal properties; it
introduces no new structural premise.

Let `S` be any scheme, `i : H ⟶ G` a homomorphism of group schemes over `S`
whose underlying morphism over `S` is monic, and `q : G.X ⟶ Q` a morphism
to any scheme `Q` over `S`. Assume the exact all-test fiber condition

`g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier U`

for every test scheme `U : Over S` and every pair of points `g,h` of `G`
over `U`. The construction
`HomogeneousCosetRelation.quotientDiagonalIso i q hfib` is an actual
scheme isomorphism from the right-coset arrow scheme `(G.X ⊗ H.X).left`
to the pullback of the diagonal of `Q` along the product map
`(q ⊗ₘ q).left`. Neither smoothness nor openness is needed for this
isomorphism, and `Q` need not carry a group structure.

To construct it, `quotientArrow` chooses a subgroup-valued difference
between any two source points with equal quotient images, using the actual
range membership in the fiber condition. Multiplying the first point by
that difference gives the second point. The endpoint formulas prove
`isPullback_diagonal_of_fibers`: the coset relation inclusion is the inverse
image of the quotient diagonal. A cone over this square yields two source
points with equal images, hence an arrow. Monicity of `i` gives uniqueness
of that arrow. Forgetting the base retains the pullback square, whose
canonical comparison with the chosen scheme pullback is the selected
isomorphism.

`etale_of_open_subgroup_quotient` adds these hypotheses: the structure map
of `G` is smooth, the underlying scheme map of `q` is smooth and
surjective, and the underlying scheme map of `i` is an open immersion.
Its conclusion is `Etale Q.hom`, still over the arbitrary base `S`.
There is no affineness, separation, quasi-compactness, normality, or
connectedness premise.

The right-coset relation inclusion is a base change of `i` along the
right-difference map, so it is an open immersion. The constructed square
identifies it as the pullback of the quotient diagonal. The product map
`q ⊗ₘ q` is flat, surjective and locally of finite presentation: each of
these properties is stable under base change and composition, and holds
for the smooth surjective map `q`. Descent of open immersions along this
map proves that the diagonal of `Q` is open. Thus `Q.hom` is formally
unramified. Independently, `q.left ≫ Q.hom = G.X.hom` is smooth, and
smoothness descends along the smooth surjective map `q.left`, giving
smoothness of `Q.hom`. Its flatness and local finite presentation, together
with formal unramifiedness, prove that `Q.hom` is étale.
