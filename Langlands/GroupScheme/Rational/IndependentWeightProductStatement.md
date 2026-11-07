# Products of additive embeddings with independent torus weights

This internal proposition is a general geometric prerequisite for the split
Steinberg immersion. It is stated here and is not proved here. It is independent
of reductive group structure or root-system classification.

`IndependentWeightProductImmersionStatement.{u}` quantifies over any field
`k : Type u`, an actual affine group scheme `G` over `Spec k`, an actual split
torus `S`, and an automorphic action `b` of `S` on `G`. For any natural number
`r`, it takes supplied group-scheme homomorphisms `y i : Ga → G` which are
closed subgroup inclusions, together with weights `w i` in the actual character
lattice of `S`. The weights must be linearly independent over `ℤ`. On every
scheme test, the action on the image of `y i` must be scalar multiplication
by the value of the character `w i`. The conclusion is that the actual ordered
product morphism from standard affine `r`-space to `G` is a closed immersion.
The field may be finite, imperfect, or of positive characteristic, and `r = 0`
is included. No smoothness or connectedness of `G` is assumed.

`IndependentWeightProduct.point y T c` is the increasing `Fin r` ordered
product of the images of the additive points with global coordinates `c i`.
`morphism y` evaluates this formula at the standard coordinate sections on
`VectorGroup.groupScheme k r`. `point_comp` proves naturality by pushing
precomposition through the list product and using the scalar-point pullback
law. `comp_morphism` gives its ordered formula on every scheme test. This
morphism is used only as a scheme morphism, with no multiplicativity claim.

The proposition is an internal coordinate-algebra criterion, motivated by the
published split Steinberg product. Its expected proof uses the split-torus
weight decomposition of affine coordinate rings. Restriction along each closed
axis supplies its linear coordinate; a lift in the corresponding weight space
pulls back to a scalar multiple of the same coordinate on affine `r`-space,
because independence of the weights excludes every other monomial of that
weight. Restriction along the axis fixes the scalar as one. These lifts make
coordinate pullback surjective. This paragraph describes a proposed proof,
not a proof implemented by this file. The proposition asserts no existence
of weights, root maps, pinnings, or normalizer representatives.
