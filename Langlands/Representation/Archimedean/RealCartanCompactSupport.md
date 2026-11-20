# Support of the real Cartan compact column

At a frame `y`, the compact test argument with left compact factor `h`
is the product of the inverse signed orthogonal part of `y * g`,
the inverse of `h`, and `y`. This is continuous on the product of
the two orthogonal groups.

If the argument is the identity, the signed orthogonal part of `y * g`
is `h⁻¹ * y`. Multiplying `y * g` by the transpose of its signed
orthogonal part gives an upper triangular matrix. The conjugate of `g`
by `y` is thus an upper triangular matrix times `h⁻¹`. When `h` is block
diagonal for ordered coordinate blocks, this product is upper triangular
by those blocks. A compact family of arguments that omits the identity
has a closed image, so tests supported in its open complement vanish on
the family.

For a permutation assigning each source block to a target block, the
proof restricts the permutation to obtain injections of coordinate
fibers. If two distinct source blocks go to the same target block,
the disjoint union of their fibers also embeds in the target fiber.
When target blocks have at most two coordinates, a source pair fills
its target block and shares it with no other source block. This gives
an injection from the source pairs to the target pairs. If the counts
are equal, this injection is onto. Two distinct singleton source blocks
cannot then share a target block, since that target would be a pair
already filled by a source pair. The block assignment is surjective
because the coordinate permutation is surjective, and its fiber maps
give the size equalities.

`RealCartanCompactSupportStatement` combines the block triangularity
argument with the fixed-flag theorem for normal Cartan matrices and
the fiber count. At an identity argument it gives a matching coordinate
permutation, with all entries of each frame column in its assigned
target block. The source pair count is at most the target pair count.
At equality it also gives the size-preserving bijection of labels.

These are internal calculations for restricting the compact column
trace to its fixed block flags.
