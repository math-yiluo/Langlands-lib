# Exact Lie support of homogeneous vector-coordinate blocks

This internal construction uses an affine group scheme with supplied natural
homogeneous vector coordinates over an arbitrary field and universe. Diagonal
action implies scalar linearity. The proved original-action/differential
comparison then computes the actual differential in these coordinates.

The standard coordinate vectors define a genuine finite basis of the actual Lie
kernel, through the inverse of `vectorLieCoordinates`. Each basis vector has
its assigned actual character as an all-test differential weight. The epsilon
coefficients characterize tangent membership in every coordinate block.
Expanding in the basis bounds the tangent space by the sum of its assigned
weight spaces. Assuming the acting commutative group scheme `S` is a split torus,
the split-torus direct-sum theorem, applied to the supplied finite
coordinates, excludes every other character. Each allowed basis vector supplies
a nonzero witness for its label. Thus the actual support of a block is exactly
the image of its allowed labels, including zero or repeated labels.

Under the same split-torus hypothesis, the block selected by any additive
subsemigroup is a smooth connected invariant
closed subgroup with support in that semigroup, so it is one of the generators
defining the actual `semigroupSubgroup`. This gives the reverse containment.
Together with the previous conditional upper containment, it identifies the
semigroup subgroup with the selected coordinate block under the two explicit
hypotheses: `S` is a split torus and
`AugmentationLieContainmentStatement` holds. The homogeneous-coordinate data
alone do not assert splitness.

The construction permits empty coordinate sets and empty semigroups. It does
not prove the general coordinate/Lie comparison or the full ordered semigroup
product theorem.
