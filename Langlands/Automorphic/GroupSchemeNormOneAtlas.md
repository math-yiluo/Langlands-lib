# The embedded Lie atlas of `G(F∞)¹`

**Sources.** J. Arthur, *An introduction to the trace formula* (2005), §13, printed p. 70 (PDF p. 82), in `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`. The space `C^r(G(F) \ G(𝔸_F)¹ / K₀)` consists of the functions that are right invariant under the open compact subgroup `K₀` of `G(𝔸_fin)` and of class `C^r` as functions on the subgroup `G(F∞)¹ = G(F∞) ∩ G(𝔸_F)¹`. Arthur writes `G(ℝ)¹` for `F = ℚ` and uses the Lie group structure of this closed subgroup of `G(ℝ)`. The definitions used here are those of [GroupSchemeNormOneSmooth](GroupSchemeNormOneSmooth.md).

All declarations are in `Langlands.Automorphic.GroupSchemeFunctions`.

## Existence of the atlas

`exists_normOneLieAtlas F G hG`: let `F` be a number field and `G` a connected reductive `F`-group scheme. Then for some `e : ℕ` there is a `NormOneLieAtlas F G hG.smoothDimension_spec e` on the actual subgroup `infiniteNormOneSubgroup F G` of the actual infinite adelic points. Such an atlas consists of a charted space on `Fin e → ℝ` in the subspace topology, a smooth manifold and real Lie group structure, and the condition that the inclusion into the [infinite adelic manifold](../Global/ReductiveInfiniteAdelicManifold.md) is a `Manifold.IsImmersion`. Affineness of `G` comes from connected reductivity (`IsConnectedReductive.affineScheme`). The atlas of the ambient group is the one fixed by `IsConnectedReductive.smoothDimension_spec`.

The proof is the closed-subgroup theorem in the form of [ClosedSubgroupImmersion](../Geometry/Manifold/LinearLieGroup/ClosedSubgroupImmersion.md):

- `G(F∞)`, with the atlas `InfiniteAdelicGroupPoints.reductiveChartedSpace F G hG`, is a manifold (`reductiveIsManifold`) and has a closed linear realization `ρ` in the units of `ArchimedeanMatrix F N` for some `N` (`InfiniteAdelicGroupPoints.exists_isClosedLinearRealization`, [InfiniteAdelicLinearRealization](../Global/InfiniteAdelicLinearRealization.md));
- `G(F∞)¹` is closed in `G(F∞)` (`isClosed_infiniteNormOneSubgroup`);
- the atlas has dimension `subgroupDim`, the dimension of the Lie algebra of `ρ(G(F∞)¹)`, and its fields are `subgroupChartedSpace`, `subgroupIsManifold`, `subgroupLieGroup` and `isImmersion_subtype`.

The charts are the exponential charts of the closed matrix group `ρ(G(F∞)¹)`, read in a basis of its Lie algebra. The section uses the operator norm on matrices (`Matrix.Norms.Operator`) and classical decidability for the normed algebra `ArchimedeanMatrix F N`.

`normOneLieDim F G hG` and `normOneLieAtlas F G hG` are a dimension and an atlas chosen by `exists_normOneLieAtlas`.

## Continuity of fixed-level functions

The module also proves two statements for an arbitrary embedded atlas.

- `ofInfinite_infinite_mem_normOneSubgroup`: if `z ∈ G(𝔸_F)¹` has finite component in a compact subgroup `K₀`, then its infinite component lies in `G(F∞)¹`. Indeed `ofInfinite (infinite z) = z · ofFinite (finite z)⁻¹`, and the included compact subgroup lies in `G(𝔸_F)¹` (`finiteLevelInclusion`).
- `continuous_of_isNormOneCr`: let `A` be an embedded atlas, `K₀` an open compact subgroup of the finite adelic points and `r` any order. Then every function `f` on `G(𝔸_F)¹` with `IsNormOneCr A r K₀ hK₀ f` is continuous.

For the proof, fix `x`. The set `U` of points `y` with `finite (x⁻¹ y) ∈ K₀` is an open neighbourhood of `x`. Every `y ∈ U` equals `x · a(y) · k(y)` with `a(y) = infinite (x⁻¹ y) ∈ G(F∞)¹` and `k(y) = finite (x⁻¹ y) ∈ K₀` (`mul_ofInfinite_mul_ofFinite`). Right `K₀`-invariance gives `f(y) = f(x · a(y))`. This is the slice `a ↦ f(x a)` evaluated at `a(y)`. The slice is continuous because it is `ContMDiff`, and `a(y)` depends continuously on `y`. So `f` is continuous on `U`, hence at `x`.

Both results are used in [ArthurTruncationRapidDecayReduction](../Global/ArthurTruncationRapidDecayReduction.md): the atlas supplies the Lie structure required by `TruncationRapidDecayStatement`, and continuity gives the joint measurability of a constant family of such functions.
