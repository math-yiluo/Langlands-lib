# Closed subgroups of linearly realized Lie groups

`Langlands.Geometry.Manifold.LinearLieGroup.ClosedSubgroupImmersion`. Let `G` be a group with a
charted space modelled on a real normed space `E`, and let `hρ : IsClosedLinearRealization 𝓘(ℝ, E) ρ`
be a closed linear realization `ρ : G →* 𝔸ˣ` in the units of a finite-dimensional complete normed real
algebra `𝔸` ([Realization](Realization.md)). Every closed subgroup `S` of `G` then carries a Lie group
structure in its subspace topology, modelled on `Fin e → ℝ`, for which the inclusion `S → G` is an
immersion. This is the closed-subgroup theorem in the form of an embedded Lie subgroup. Namespace
`Langlands.LinearLieGroup`; the results on `S` are in `Langlands.LinearLieGroup.IsClosedLinearRealization`
and take `hS : IsClosed (S : Set G)`.

## The charts

- `rangeHomeomorph hf : M ≃ₜ* f.range`, for a homomorphism `f : M →* 𝔸ˣ` that is a closed embedding:
  the corestriction, an isomorphism of topological groups (`bijective_rangeRestrict_of_isClosedEmbedding`;
  the inverse is continuous because `f` is an embedding).
- `isClosedEmbedding_comp_subtype`, `isClosed_subgroupRange`: `ρ` restricted to `S` is a closed
  embedding, so `ρ(S)` is closed in `𝔸ˣ`.
- `subgroupLie hρ hS`: the Lie algebra `lieSubmodule ρ(S) _` of `ρ(S)`, and `isExpLieAlgebra_subgroup`:
  `ρ(S)` carries exponential charts for it (`isExpLieAlgebra_of_isClosed`, von Neumann's theorem in
  [ClosedSubgroup](ClosedSubgroup.md)).
- `subgroupDim hρ hS`, the dimension of `subgroupLie`, and `subgroupCoord`, the linear coordinates
  `subgroupLie ≃L[ℝ] (Fin subgroupDim → ℝ)` given by `Module.finBasis`.
- `subgroupHomeomorph : S ≃ₜ* ρ(S)`, `rangeHomeomorph` for `ρ` restricted to `S`.
- `subgroupChart hρ hS s`: the exponential chart of `ρ(S)` at `ρ s`, transported to `S` by
  `subgroupHomeomorph` and read in `subgroupCoord`. Its inverse is `X ↦ ρ⁻¹(ρ s · exp X)`
  (`subgroupChart_symm_apply`), its source is the set of `y` with `ρ(s)⁻¹ ρ(y)` in the neighbourhood
  `nhdOne` of the exponential structure (`mem_subgroupChart_source`), and its target is the set of `X`
  whose vector lies in the neighbourhood `nhd` (`mem_subgroupChart_target`).
- `subgroupChartedSpace hρ hS : ChartedSpace (Fin subgroupDim → ℝ) S`, with atlas the range of
  `subgroupChart` and `chartAt = subgroupChart`. It is a definition, installed with `letI`, because
  the subtype `S` may already carry other structure.

## The Lie group structure

- `subgroupIsManifold hρ hS n`: with these charts `S` is a `C^n` manifold for every `n`. The
  transition map from the chart at `s` to the chart at `s'` is `X ↦ L (proj (log (c exp (L⁻¹ X))))`
  with `c = ρ(s')⁻¹ ρ(s)`, `L = subgroupCoord` and `proj` the projection onto the Lie algebra; it is
  smooth by `IsExpLieAlgebra.contDiffOn_proj_symm_mul_exp`.
- `contMDiff_subgroup_val`: `s ↦ ρ s`, as a map `S → 𝔸`, is smooth. In the chart at `s` it is
  `X ↦ ρ(s) exp (L⁻¹ X)`.
- `isEmbedding_subgroup_val`: `s ↦ ρ s` is a topological embedding of `S` in `𝔸`.
- `contMDiffAt_subgroup_of_val`: a map `f` from a manifold into `S` is `C^n` at `x` when
  `y ↦ ρ (f y)` is `C^n` at `x`. Continuity of `f` comes from the embedding; in the chart at `f x`
  the map is `L ∘ proj ∘ log` applied to `ρ(f x)⁻¹ ρ(f y)`, and the logarithm is smooth near `1`.
- `subgroupLieGroup hρ hS n`: `S` is a `C^n` Lie group. Multiplication and inversion are tested through
  `ρ` by the previous criterion: they become multiplication and `Ring.inverse` in `𝔸`.

## The immersion

- `nonempty_equiv_of_contMDiff_inverse`: if smooth maps `φ : M → N` and `ψ : N → M` are inverse to
  each other, then the model spaces of `M` and `N` are linearly isomorphic; the derivatives of `φ`
  and `ψ` at corresponding points are inverse to each other by the chain rule.
- `exists_lieSubmodule_equiv_model`: the Lie algebra of `ρ(G)` is linearly isomorphic to `E`. Apply the
  previous lemma to `rangeEquiv` and its inverse, which are smooth for the exponential charts of
  `ρ(G)` (`contMDiff_rangeRestrict_and_symm` of [Realization](Realization.md)).
- `subgroupLie_le`: the Lie algebra of `ρ(S)` lies in that of `ρ(G)`.
- `isImmersion_subtype hρ hS` (for `[IsManifold 𝓘(ℝ, E) ∞ G]`): the inclusion `S → G` is a
  `Manifold.IsImmersion` for the charts `subgroupChart` on `S`. At `s ∈ S` take on `G` the chart
  `codChart`: the exponential chart of `ρ(G)` at `ρ s`, pulled back to `G` by `rangeEquiv` and
  followed by the isomorphism `Λ` of `exists_lieSubmodule_equiv_model`. This chart lies in the maximal
  atlas of `G` because `rangeEquiv` and its inverse are smooth. Choose a complement `W` of the Lie
  algebra of `ρ(S)` in that of `ρ(G)`. In these charts the inclusion is `X ↦ Λ (L⁻¹ X)`, that is,
  `X ↦ equiv (X, 0)` for the linear isomorphism `equiv : (Fin subgroupDim → ℝ) × W ≃L[ℝ] E`, because the
  logarithm of `exp (L⁻¹ X)` is `L⁻¹ X` near `0` (`IsExpLieAlgebra.symm_exp`) and the projection onto
  the Lie algebra of `ρ(G)` fixes it. This is `Manifold.IsImmersionAtOfComplement` at every point.

## Literature

The closed-subgroup theorem: every closed subgroup of a real Lie group is an embedded Lie subgroup in
the subspace topology. For matrix groups see B. C. Hall, *Lie groups, Lie algebras, and
representations*, 2nd edition, GTM 222 (2015), §3.8, Corollary 3.45, p. 70, and Theorem 3.42, p. 68.
Hall's proof makes the matrix group locally the exponential of its Lie algebra, which is what the
charts `subgroupChart` do. The module transfers the linear statement of
[ClosedSubgroup](ClosedSubgroup.md) to a closed subgroup of an abstract Lie group through a closed
linear realization, and proves the immersion property in explicit charts.

## Use

`Langlands.Automorphic.GroupSchemeFunctions.exists_normOneLieAtlas`
([GroupSchemeNormOneAtlas](../../../Automorphic/GroupSchemeNormOneAtlas.md)) applies the module to the
closed subgroup `G(F∞)¹` of the archimedean points of a connected reductive group.
