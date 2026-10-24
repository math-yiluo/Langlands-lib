# Identity-fibre trivializations and the balanced cube faces

This internal construction connects a supplied trivialization at the group
identity with the constant-factor input of the published balanced cube face
comparisons. It works for any scheme `S` and any group object `G` in `Over S`,
in every universe. No commutativity or geometric conditions are needed.

`identityFibre G L` is the actual module-sheaf pullback of `L.obj` along the
identity section `1 : Over.mk (𝟙 S) ⟶ G.X`. The numeral denotes the unit in
the pointwise group of maps, so it is the identity section of the group object.

`constantIdentityIso G L T e` takes an actual isomorphism
`e : identityFibre G L ≅ structureSheaf S` and returns an isomorphism from
the pullback along `1 : T ⟶ G.X` to `structureSheaf T.left`. To construct
it, let `q` be the unique map from `T` to `Over.mk (𝟙 S)`. The group-object
identity `MonObj.comp_one` identifies `q ≫ 1` with the constant identity map
on `T`. The inverse of `pullPullIso` identifies pullback along this composite
with the iterated pullback. Applying the pullback functor to `e` and then
`pullbackUnitIso q.left` gives the required actual isomorphism. Tensor
preservation is not needed for this construction.

The three constructions `firstFaceIsoOfIdentityFibre`,
`secondFaceIsoOfIdentityFibre`, and `thirdFaceIsoOfIdentityFibre` specialize
`constantIdentityIso` to `T = G.X ⨯ G.X` and pass the result to the
corresponding published face comparison. Each additionally requires the
explicit input `preservation : pullbackTensorComparisonIsIsoStatement`.
Their endpoints are the pullbacks of `cubePositive G L` and
`cubeNegative G L` along the actual first, second, and third `CubeFace` maps.
They compare the two face restrictions; they do not trivialize either
restriction individually.

The pullback-composition transport is adapted from Worker 316's private
`lineBundle_constant_pullback_trivial` construction in shared draft revision 1
of task `4db6f774-722f-405b-aeaa-8ab052f17c14`,
`Langlands/AbelianScheme/FieldSymmetricMultiplicationPullbackProof.lean`.
Worker 316 is a coauthor. Here the field-specific existence argument is removed:
the trivialization `e` is supplied explicitly, the base is an arbitrary scheme,
and the constant map is identified using the group-object unit law. Only
published pullback constructors and the published balanced cube helpers are
imported. The unreviewed draft is an authorship and construction source, not
an assumed mathematical result.

This is derived categorical infrastructure for the identity-face calculation
in the balanced cube argument. It does not prove that `identityFibre G L` is
trivial, even when `S` is a field spectrum. The field-triviality theorem,
tensor-preservation theorem, and global cube comparison remain separate
obligations. In particular, this module does not prove
`FieldCubePullbackStatement`.
