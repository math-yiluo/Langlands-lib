# Scalar extension of the actual external-action weights

This internal construction concerns the actual automorphic action of a split
torus on an affine group scheme locally of finite type over a field. No
embedding of the acting torus into the group is assumed. The field and every
extension field lie in an arbitrary common universe.

`extendedActionWeightSpace` is the scalar span of an original intrinsic action
weight space in the actual Lie kernel of the pulled-back group. The embedding
uses the published tensor scalar-extension isomorphism and scheme pullback
comparison, not a replacement representation.

The comparison of the actual action differentials under scheme pullback and
the comparison of actual character values show that every original weight
vector extends into its prescribed weight space. Tensor induction shows that
the extended spaces span the whole pulled-back Lie algebra. The internal
direct-sum decomposition for the actual split-torus action then identifies
each pulled-back weight space with the sum of extended spaces in its character
fiber. The published bijectivity of character pullback for a split torus reduces
that fiber to a single original character.

Faithful scalar extension preserves and reflects nonvanishing of each
extended span. Consequently
`actionWeightSpace_baseChange_ne_bot_iff` and
`mem_actionWeightSupport_top_baseChange_iff` preserve and reflect the complete
intrinsic support of the whole group. These assertions include zero whenever
it is an occurring character; they do not filter to nonzero roots.

The provenance is internal, combining the published differential pullback,
Lie tensor scalar extension, split-torus weight decomposition and character
lattice pullback. This unit does not identify arbitrary subgroup tangent images
or semigroup subgroups after field extension, and does not establish the full
ordered semigroup product theorem.
