# The subgroup homomorphisms of ordered projector families

Fix weights in an additive character group and an ordered projector family over the global functions of a scheme over `Spec R`. The points of the pulled-back diagonalizable group are characters with values in global units. Evaluating the fixed weights gives the unit scalars on the summands of the projector family. The corresponding invertible matrix gives a point of the pulled-back general linear group. Restriction of functions commutes with the weighted matrix construction, so these point maps define the actual homomorphism `subgroupHom`.

Over `Spec A`, the canonical base-change comparisons identify this with the group-algebra representation of the projectors on `A`. The global functions isomorphism preserves the family, and the comparisons preserve the character and matrix coordinates on every test scheme. For generating weights, the coordinate algebra surjectivity theorem for that representation gives `isClosedSubgroup_subgroupHom_spec`.

This is an internal construction connecting the affine ordered projector chart to the actual closed subgroup functor of the general linear group.

The affine ordered projector scheme carries the family corresponding to its identity point. When the weights generate and the diagonalizable source is a split torus, this gives an admissible subgroup. `chartMap` classifies it using the given universal subtorus family, and `evaluate_chartMap` identifies the classified subgroup with the range of the universal projector homomorphism.
