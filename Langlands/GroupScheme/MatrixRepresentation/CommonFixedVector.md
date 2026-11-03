# Common fixed vectors for unipotent factors

This derived internal argument constructs a nonzero vector fixed by two affine
unipotent factors in a nonzero finite matrix representation of an ambient group
scheme over any field. The finite coordinate index `n` is nonempty. The first
factor has normal all-test image. No smoothness, connectedness, perfectness, or
rational-point density is assumed.

`exists_subspace_coordinates` chooses a finite basis of a subspace and a linear
retraction onto it. The matrices of the inclusion and retraction satisfy
`C * B = 1`, every vector in the image of `B` belongs to the subspace, and
`B * C` fixes the subspace.

For `exists_common_fixedVector_of_affine_models`, the nonempty coordinate index
permits applying unipotence of the first factor to obtain a nonzero vector in
its all-test fixed subspace, which therefore has positive dimension. The
coordinate lemma gives matrices for this subspace. Normality and the published tensor coefficient argument in
`NormalFixedCoordinates` show that the second factor preserves these coordinates.
The published `restrictCoordinates` constructs the actual group-scheme
representation on them. Unipotence of the second factor yields a nonzero fixed
coordinate vector. Its inclusion is nonzero because `C * B = 1`, is fixed by the
first factor by subspace membership, and is fixed by the second by the
intertwining identity. The final `exists_common_fixedVector` chooses affine
models using the essential-image description of the relative spectrum functor.

The Prop-valued `HasCommonFixedVector` predicate records the existence of this
nonzero vector with both all-test fixedness properties.

Both existence theorems retain the nonempty coordinate-index hypothesis.
Both unipotence assumptions are used. The conclusions use the unchanged
`IsFixedVector` predicate on all relative scheme tests and retain universe `u`.
This is matrix and finite-dimensional linear algebra applied to the published
definitions; it invokes no external structural theorem on algebraic groups.
