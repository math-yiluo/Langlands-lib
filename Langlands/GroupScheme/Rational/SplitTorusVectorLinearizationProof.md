# Linearization of split-torus actions on whole vector groups

`Langlands.GroupScheme.RelativeRoot.splitTorusVectorLinearization` proves the
exact published proposition `SplitTorusVectorLinearizationStatement.{u}` at
arbitrary universe `u`. It applies to every algebraically closed field, every
actual vector group, and every actual automorphic action of a split torus.

The proof reuses the stronger published theorem
`Langlands.GroupScheme.RelativeRoot.torusVectorActionLinearization` from
`Rational/TorusVectorLinearizationProof`, which treats arbitrary fields and
arbitrary tori, with a specified vector-group dimension. Unpack
`IsVectorGroup V` to obtain its dimension `n` and witness
`IsVectorGroupOfDimension V n`. The published `IsSplitTorus.isTorus` makes the
supplied split torus eligible for the general theorem. That theorem returns
coordinates `e` and the literal `IsLinearVectorCoordinates b e`; package them
with the same `n`.

The resulting coordinates are natural on every scheme over the field. The
actual action commutes with multiplication by every global function on each
test scheme, including nonaffine and nonreduced tests. The group equivalences
already supply additivity. The construction imposes no restriction on weights,
the fixed subgroup, or the dimension, so zero and repeated weights, dimension
zero, and the trivial group are retained. No factor is removed.

This proof is an internal specialization of published mathematics. It assumes
no classification or decomposition statement beyond the imported proved
torus-linearization theorem. The general theorem's paired Markdown explains
its characteristic-zero and additive-polynomial proof routes and their
comparison with the source passages cited by the target statement.
