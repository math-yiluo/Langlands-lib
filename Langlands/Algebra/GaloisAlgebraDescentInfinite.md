# Noncommutative fixed tensors over arbitrary Galois extensions

This internal generalization removes finite-dimensionality of the
field extension from the published fixed-tensor theorem in
`GaloisAlgebraDescent`. It uses Mathlib's
`InfiniteGalois.mem_range_algebraMap_iff_fixed`, which identifies the
elements of an arbitrary Galois extension fixed by all its ground-field
automorphisms with the original field.

Choose a basis of the possibly noncommutative algebra factor. A fixed
tensor's coefficients in the extended basis are fixed field elements,
by the published coefficient-action coordinate formula. Lift each to
the ground field, and sum over the tensor's finite coordinate support
to construct its original algebra element. The extended-basis
reconstruction formula proves the desired equality. The forward
implication is the coefficient action fixing a pure tensor `1 tensor a`.

Neither the field extension nor the algebra is required to be
finite-dimensional. The field, extension and algebra have arbitrary
possibly distinct universes. There is no characteristic, perfection,
commutativity-of-the-algebra, continuity or effectivity premise.
