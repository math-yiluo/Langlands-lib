# The composed and flattened opposite radicals

`Langlands.Parabolic.flattenedOppositeUnipotentComparison` proves the exact
published proposition `FlattenedOppositeUnipotentComparisonStatement`.
For every commutative ring, natural rank, ordered block shape and ordered
refinement, the actual inverse-image composed opposite radical equals the
opposite radical of the actual flattened shape as subgroups of the same
general linear group.

The proof establishes both subgroup inclusions using the published
matrix-entry characterizations of the opposite parabolic and radical.
Starting with the flattened radical, it expresses each coordinate of an
outer block in the coordinates of its inner block. The actual nested
coordinate identity `index_index_eq_flatten` and the lexicographic order
formula `flattenBlockEquiv_lt_iff` show that the matrix lies in the outer
opposite parabolic. Its projected diagonal blocks lie in the respective
inner opposite parabolics and have identity fine diagonal blocks.
The casts between equal block sizes preserve coordinate equality. The
inverse-image membership criterion then gives the composed radical.

Conversely, a matrix in the composed radical is lower triangular in
outer blocks, and each projected outer diagonal block lies in its inner
opposite radical. Two strictly ordered flattened blocks either have
strictly ordered outer blocks or share their outer block and have
strictly ordered inner blocks. The corresponding outer or inner
triangularity gives the required zero entry. The identity fine diagonal
blocks follow from the inner radical condition. Here `flatten_index`
identifies the actual flattened coordinates with their nested coordinates,
and `oppositeLeviProjection_apply` identifies the projected entries with
the original matrix entries.

This is an internal finite matrix argument from the existing definitions
in `OppositeRefinementDefinitions`, the opposite entry criteria in
`Group.GL.OppositeBlocks`, and the constructed ordered flattening in
`CuspidalSupport.MinimalJacquetProof`. It uses no external literature
claim or supplied coordinate identification. No nonempty-rank,
nontrivial-ring, field or representation hypothesis is added; rank zero
is included. This theorem supplies only the literal subgroup equality.
The comparison of normalized Jacquet representations additionally
requires comparison of the actual modulus characters and actions.
