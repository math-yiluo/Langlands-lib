# Exact ordered semigroup products for actual linear vector actions

This internal development treats an affine group scheme over any field in an
arbitrary universe, equipped with homogeneous natural vector coordinates for
the original action of a split torus. Its full actual Lie-weight support is
exactly the range of the supplied coordinate labels: the full coordinate block
is the top subgroup, so the previously proved exact block-support calculation
applies.

`weightBlockIndices` takes the inverse image of each given weight block under
the actual label map. A disjoint covering of the full Lie support therefore
partitions the coordinate indices. The exact CGP cross-exclusion assumption
states that each block is disjoint from the positive additive semigroup generated
by any distinct block. Every occurring label belongs to one original block.
Consequently it can belong to another block's generated semigroup only if those
blocks coincide. Thus positive closure selects exactly the original coordinate
block. This argument does not assume that the generated semigroups themselves
are pairwise disjoint.

Assuming additionally
`CoordinateWeights.AugmentationLieContainmentStatement`, the previously proved
semigroup-subgroup equality identifies each generated subgroup with this
coordinate block. The existing coordinate-block realization supplies actual
smooth connected closed representatives. Applying the proved coordinate-partition
product theorem to these same inclusions proves that their original
`orderedMultiplication` is an isomorphism of schemes. The final theorem first
constructs homogeneous coordinates from any supplied natural scalar-linear
vector coordinates, so it needs no independently supplied homogeneous basis.

All tests and coordinate maps are the existing actual scheme and Lie-kernel
constructions. No restriction on characteristic, ordering, dimension, repeated
labels or the occurrence of zero is added. The index set may be empty; its
covering assumption then forces empty actual Lie support and empty coordinate
indices. Positive additive semigroup closure does not automatically insert zero.

This proves the vector case under the explicit coordinate/Lie support-comparison
hypothesis. It does not prove that comparison, the central-unipotent induction,
or the full `SemigroupOrderedProductStatement` for arbitrary solvable groups.
