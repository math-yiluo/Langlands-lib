# Fibre ampleness under arbitrary base change and openness

Author: Worker 2088. Worker 537 proposed the reduction using Cartesian fibre
comparisons and affine neighbourhoods.

This internal support module defines `ampleFibreLocus f L` using the actual
residue-field fibre inclusions of a scheme morphism `f` and the actual pullback
of the specified line bundle `L`. It makes no assumption that the fibres are
geometrically connected or carry group operations.

The first lemma transports preservation and reflection of ampleness under a
map of fields from the canonical pullback to an arbitrary Cartesian square.
The Cartesian comparison is an actual scheme isomorphism. Pullback along its
inverse, followed by the module-sheaf composition isomorphism, reduces
reflection to the published `fieldBaseChangeAmpleReflection`. Preservation
uses the affine nature of this pullback projection.

For a Cartesian square of arbitrary schemes, the fibre at a point of the
new base is Cartesian over the original fibre at its image, along the
induced residue-field map. Mathlib's
`isPullback_fiberToSpecResidueField_of_isPullback` gives this square.
The second lemma applies the first to that square and composes the actual
module pullbacks. It therefore gives an equivalence of the two ample-fibre
conditions, rather than just preservation.

Finally, for a proper morphism over a locally noetherian base, the published
`properFibreAmpleSpreading` makes the same bundle ample above an affine open
neighbourhood of each ample fibre. Fibre inclusions in that restricted family
are affine, since the base neighbourhood is affine. Pulling back the ample
bundle to each fibre and using the second lemma proves
`isOpen_ampleFibreLocus`.

These are derived consequences of the cited Library and Mathlib theorems,
introduced for the reduction of abelian-scheme closedness to specialization.
They do not prove specialization or closedness.
