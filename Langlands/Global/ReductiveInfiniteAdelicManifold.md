# Infinite adelic manifolds from connected reductivity

This is an internal application of existing Library theorems. It constructs
specified completion and infinite adelic manifolds directly from
`Langlands.GroupScheme.IsConnectedReductive G`, without an additional dimension,
rank or analytic premise. It imports the original predicate and point groups.

For a field `F : Type u`, let `G` be a group scheme over `Spec F` and
`hG : IsConnectedReductive G`. In the predicate's namespace:

- `exists_smoothOfRelativeDimension` applies
  `Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension` to the structure
  morphism, using `hG.smooth` and `hG.connectedSpace`. It proves that the
  structure morphism is smooth of some constant natural relative dimension.
- `smoothDimension` chooses the least such natural number with `Nat.find`;
  `smoothDimension_spec` proves the corresponding relative-dimension property.
  This choice fixes a dimension for the charts used below.
- `affineScheme` obtains affineness of the underlying scheme from the
  predicate's affine structure morphism and affineness of the field spectrum.

The dimension existence theorem already has a published proof in
`Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof`. This file
specializes it; it introduces no additional algebraic theorem as an assumption.

For any infinite place `v` of the field, the namespace
`Langlands.Global.InfinitePlaceGroupPoints` supplies:

- `reductiveChartedSpace`, the atlas `smoothChartedSpace F G v
  hG.smoothDimension_spec` on the actual group of completion-valued points;
- `reductiveIsManifold`, its real smooth manifold structure with model
  `Fin hG.smoothDimension → v.Completion`;
- `reductiveLieGroup`, smoothness of the existing multiplication and inversion
  with that atlas and model;
- `reductive_contMDiff_iff_coordinateSmooth`, the equivalence between smooth
  families into these specified charts and `G.CoordinateSmooth` using all
  regular functions, completion coefficients and the identity coefficient map.

The manifold and smoothness results explicitly select the existing
`completionRCLike F v` instance. These local results require only the stated
field structure and infinite place; the finite product below additionally
requires a number field.

For `[NumberField F]`, the namespace
`Langlands.Global.InfiniteAdelicGroupPoints` supplies the corresponding
`reductiveChartedSpace`, `reductiveIsManifold` and `reductiveLieGroup` on the
original infinite adelic point group. The model is
`smoothModel F hG.smoothDimension`, the finite dependent product of the
completion models. The atlas is exactly the earlier `smoothChartedSpace`
specialized to `hG.smoothDimension_spec`. Consequently the Lie-group operations
are the original adelic group operations.

`reductiveCompletionsDiffeomorph` equips the existing completion decomposition
with the specified infinite adelic atlas and the earlier `productChartedSpace`
on the product of completion-valued point groups. Both model spaces are the
same finite dependent product. The theorem
`reductiveCompletionsDiffeomorph_toEquiv` proves by reflexivity that its underlying
equivalence is `(completions F G).toEquiv`.

The global `reductive_contMDiff_iff_coordinateSmooth` characterizes smooth
families by the original mixed-coordinate condition. Its coefficient map is
`(InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom`, and its target coefficient
algebra is `mixedEmbedding.mixedSpace F`. Both the local and global criteria
allow an arbitrary charted source `M` with any real model with corners `I`.
They assume no manifold compatibility for that source. Each result is a direct
application of its previously constructed smooth-relative-dimension interface.

Every manifold, Lie-group and family statement specifies the selected affine,
completion-scalar and chart instances by local `letI` binders. These are named
constructions, rather than global competing chart instances. The proofs use the
same chosen dimension and the same actual decomposition throughout.

This file does not construct quotient measures, prove reduction theory or
finite volume, or compare these charts with the existing general-linear
automorphic manifolds. Those remain separate obligations of the surrounding
adelic construction.
