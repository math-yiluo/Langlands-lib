# Relative dimension and nontriviality of vector groups

The standard polynomial vector group over any commutative ring is smooth
of relative dimension equal to its number of coordinates. The Lean proof
uses the standard smooth presentation of a polynomial algebra, passes to
the associated spectrum map, and uses the locally standard smooth
criterion for smooth relative dimension.

Over a field, natural vector coordinates supply the actual isomorphism
`IsVectorGroupOfDimension.iso` constructed in `VectorGroupCoordinates`.
Transporting the preceding relative-dimension calculation along this
isomorphism proves `SmoothOfRelativeDimension n V.X.hom` from
`IsVectorGroupOfDimension V n`. Dimension zero is included.

The remaining statements are elementary consequences of the all-test
coordinate equivalences. Every point of a zero-dimensional vector group
is the identity, because a function on `Fin 0` is unique. Consequently
every homomorphism from such a group has the trivial subgroup functor as
its image. Contraposition shows that any nontrivial image forces positive
coordinate dimension; the homomorphism need not be injective. Finally,
points of a vector group commute, because their coordinates form an
additive commutative group. `IsVectorGroupOfDimension.pointsCommGroup`
packages this fact as a commutative group structure on each test-point
group, preserving its existing multiplication, identity and inversion.

This internal unit uses the existing polynomial standard smoothness
instances and natural-coordinate comparison. It supplies geometric and
nontriviality consequences for the stable-vector subgroup target. It
does not construct a stable subgroup or prove a conjugacy theorem.
