# Level towers of schemes reindexed along level functors

This internal construction restricts a level tower of schemes, its
coefficients and its colimit cohomology along a level functor. Let `H` and
`G` be groups with topologies, let `φ : H →* G` be a group homomorphism and
let `Φ : FunctorOver φ` be a level functor over `φ`. A level tower
`T : CompactOpenLevel G ⥤ Scheme.{u}` then gives the reindexed tower
`Φ.functor ⋙ T`, with schemes `T (Φ K)` for the levels `K` of `H`. The module
shows that the hypotheses of the published level-tower cohomology are
inherited by the reindexed tower. It compares the colimit cohomology of the
reindexed tower `H`-equivariantly with that of `T`, and records how
reindexing interacts with pulled-back coefficients, base change and the
Galois action. All declarations are in namespace
`Langlands.Shimura.ReindexLevelTowerCohomology`.

## Motivation and scope

Proposition 4.10 on printed p. 311 of Harris (1999), *Galois properties of
cohomological automorphic forms on GL(n)*, ends with the statement that its
spectral sequences are `GG(A_f^{ℓ,p})`-equivariant as the level
`K(N)^{ℓ,p}` varies. There the cohomology of a Shimura tower is taken over the
levels whose component at `ℓ, p` is fixed. Those levels form the image of a
level functor over the inclusion of the away factor. This module supplies the
general restriction of tower cohomology along such a functor. The module
`Langlands.Shimura.SplitLevelTowerCohomology`, submitted together with this
one, applies it to a splitting of the group.

The module constructs no Shimura variety, no particular level functor and no
spectral sequence. It proves no statement about finiteness, compact support
or limit schemes. Harris's passage is motivation only; no statement from it
is formalized.

## Inputs

The published `Langlands.Shimura.Levels` provides the transporter category
`CompactOpenLevel G` of compact open subgroups of `G` and the self-arrows
`selfArrow K k hk` for `k ∈ K`.

The published `Langlands.Shimura.PartialLevelTower` provides level functors
`Φ : CompactOpenLevel.FunctorOver φ`, with underlying functor `Φ.functor`,
`Φ.map_mem` (`φ k ∈ Φ K` for `k ∈ K`) and `Φ.map_selfArrow` (`Φ` sends
`selfArrow K k hk` to the self-arrow of `Φ K` with element `φ k`). For a
presheaf `F` on the levels of `G` it provides the restriction
`LevelColimit.reindex Φ F = Φ.functor.op ⋙ F`, the comparison
`LevelColimit.reindexComparison Φ F` of colimits with
`ι_reindexComparison` (its leg at `K` is `ι F (Φ K)`) and
`map_reindexComparison` (naturality in `F`), the comparison
`reindexComparisonHom Φ F : action (reindex Φ F) ⟶ (Action.res C φ).obj (action F)`
of objects with an action of `H`, and
`translate_reindexComparison_apply_of_mem` (for a level-trivial presheaf of
modules and a nonempty type of levels of `H`, an element `g` in every image
level `Φ K` fixes the image of the comparison). The published
`Langlands.Shimura.CofinalLevelReindex` provides the predicate
`Φ.IsCofinal` (every level of `G` contains some `Φ K`) and the isomorphism
`LevelColimit.reindexActionIso F hΦ` whose forward morphism is
`reindexComparisonHom Φ F`.

The published `Langlands.Geometry.EtaleCohomologyReindex` provides, for a
compatible coefficient diagram `D` over a scheme diagram `S` and an index
functor `F`, the restriction `CoefficientDiagram.reindex F D` over `F ⋙ S`,
the functor `CoefficientDiagram.reindexFunctor F`, and the definitional
equalities `reindex_cohomology` and `reindex_sections`.

The published `Langlands.Shimura.LevelTowerCohomology` provides, for
`T` with étale level maps and a commutative ring `R`, the coefficient
diagrams `CoefficientDiagram R T.op` with cohomology presheaves
`D.cohomology q` and section presheaf `D.sections`, the predicate
`IsLevelTrivialCoefficients D` (for `k ∈ K` the self-arrow acts on `T K` by
the same scheme morphism as the identity arrow, and its coefficient map is
the identity coefficient map transported by `restrictionCongr`), the full
subcategory property `levelTrivialCoefficients T R`, the lemma
`isLevelTrivial_cohomology`, and for a topological group `G` the colimit
cohomology `colimitCohomology D q : Action (ModuleCat R) G` and the smooth
representation `smoothColimitCohomology D hD q`.

The published `Langlands.Shimura.LevelTowerCanonicalCoefficients` provides,
for projections `p : T ⟶ (Functor.const _).obj X` to a scheme `X` and a
module sheaf `M` on the small étale site of `X`, the pulled-back coefficients
`canonicalCoefficients R p M` (with sheaf `p_K^* M` at level `K`), and for a
morphism of towers `ψ : T' ⟶ T` with étale components and `hψ : ψ ≫ p = p'`
the pullback `canonicalPullback R p ψ hψ M n` of cohomology presheaves.

The published `Langlands.Shimura.LevelTowerGalois` provides, for structure
maps `s : T ⟶ (Functor.const _).obj (Spec F)` and an `F`-algebra `L`, the
base-changed tower `baseChangeTower F L s` with levels `T K ×_{Spec F} Spec L`,
its first projection `baseChangeProjection F L s`, the Galois action
`towerGaloisAction F L s`, the lemma `towerGaloisAction_over`, and the functor
`galoisCohomologyFunctor F L s p R hT n` from module sheaves on `X` to
`Action (SmoothRep R G) (L ≃ₐ[F] L)`.

## Reindexed towers and coefficients

Let `T : CompactOpenLevel G ⥤ Scheme.{u}` have étale level maps and let `R`
be a commutative ring.

- The instance `etale_reindex_map` states that the level maps of
  `Φ.functor ⋙ T` are étale; the map along `a` is `T.map (Φ.functor.map a)`.
- `reindex_selfArrow Φ hT K k hk`: if `T.map (selfArrow K k hk)` is the
  identity for every level `K` of `G` and `k ∈ K`, the same holds for
  `Φ.functor ⋙ T`. The proof rewrites with `Φ.map_selfArrow`. This lemma does
  not need the étaleness hypothesis.
- `reindexCoefficients Φ D` is `CoefficientDiagram.reindex Φ.functor.op D`, a
  coefficient diagram on the reindexed tower. The `rfl` lemmas
  `reindexCoefficients_obj` and `reindexCoefficients_map` state that its
  sheaf at `op K` is `D.obj (op (Φ K))` and its map along `a` is
  `D.map (Φ.functor.op.map a)`.
- `reindexCoefficients_cohomology Φ D q` and
  `reindexCoefficients_sections Φ D` state, by `rfl`, that the cohomology and
  section presheaves of the reindexed coefficients are
  `LevelColimit.reindex Φ (D.cohomology q)` and
  `LevelColimit.reindex Φ D.sections`.
- `isLevelTrivialCoefficients_reindex Φ hD`: reindexing level-trivial
  coefficients gives level-trivial coefficients. For `k ∈ K` it applies `hD`
  at `Φ K` and `φ k` (using `Φ.map_mem`), after rewriting the self-arrow with
  `Φ.map_selfArrow` and the identity arrow with `Φ.functor.map_id`.
- `reindexCoefficientsFunctor Φ T R` is reindexing as a functor from the full
  subcategory of level-trivial coefficient diagrams on `T` to that on
  `Φ.functor ⋙ T`. It lifts the inclusion followed by
  `CoefficientDiagram.reindexFunctor Φ.functor.op`.
  `reindexCoefficientsFunctor_obj_obj` records, by `rfl`, that its value at
  `D` has underlying diagram `reindexCoefficients Φ D.obj`.
- `cohomologyMap_reindex Φ α q`: for a coefficient morphism `α : D ⟶ E`, the
  cohomology map of the reindexed morphism is the whiskering
  `Functor.whiskerLeft Φ.functor.op (cohomologyMap α q)`, by `rfl`.

## The comparison of colimit cohomology

Assume moreover that `H` and `G` are topological groups.

- `colimitCohomologyComparison Φ D q` is
  `LevelColimit.reindexComparisonHom Φ (D.cohomology q)`, a morphism
  `colimitCohomology (reindexCoefficients Φ D) q ⟶ (Action.res (ModuleCat R) φ).obj (colimitCohomology D q)`
  of objects with an action of `H`, where `H` acts on the target through `φ`.
  `colimitCohomologyComparison_hom` records, by `rfl`, that its underlying
  map is `LevelColimit.reindexComparison Φ (D.cohomology q)`.
- `ι_colimitCohomologyComparison Φ D q K`: on the classes of level `K` of `H`
  the comparison is the colimit leg at level `Φ K` of `G`.
- `map_colimitCohomologyComparison Φ α q`: the comparison is natural in the
  coefficient morphism `α : D ⟶ E`. The colimit map of the reindexed
  cohomology map followed by the comparison for `E` equals the comparison for
  `D` followed by the colimit map of `cohomologyMap α q`.
- `translate_colimitCohomologyComparison_apply_of_mem Φ hD q hg x`: assume
  that `D` is level-trivial, that `H` has a compact open level, and that
  `g ∈ G` lies in every image level `Φ K`. Then `g` acting on
  `colimitCohomology D q` fixes the image of every `x` under the comparison.
  This is the published `translate_reindexComparison_apply_of_mem` with
  `isLevelTrivial_cohomology hD q`.
- `colimitCohomologyReindexIso hΦ D q`: if `Φ` is cofinal, the comparison is
  an isomorphism of objects with an action of `H`. It is the published
  `LevelColimit.reindexActionIso (D.cohomology q) hΦ`, and
  `colimitCohomologyReindexIso_hom` states that its forward morphism is
  `colimitCohomologyComparison Φ D q`.

## Coefficients pulled back from a base

Let `X` be a scheme and `p : T ⟶ (Functor.const (CompactOpenLevel G)).obj X`
projections of `T` to `X`.

- `reindexProjection Φ p : Φ.functor ⋙ T ⟶ (Functor.const (CompactOpenLevel H)).obj X`
  has component `p.app (Φ K)` at `K` (`reindexProjection_app`, by `rfl`).
- `reindexCoefficients_canonical Φ R p M`: for a module sheaf `M` on `X`,
  `reindexCoefficients Φ (canonicalCoefficients R p M)` is
  `canonicalCoefficients R (reindexProjection Φ p) M`, by `rfl`.

Let `T'` be a second tower with étale level maps, `ψ : T' ⟶ T` a natural
transformation with étale components, and `hψ : ψ ≫ p = p'` for projections
`p'` of `T'` to `X`.

- The instance `etale_whiskerLeft_app` states that the components of
  `Functor.whiskerLeft Φ.functor ψ` are étale.
- `whiskerLeft_reindexProjection Φ p ψ hψ`:
  `Functor.whiskerLeft Φ.functor ψ ≫ reindexProjection Φ p = reindexProjection Φ p'`,
  checked componentwise from `hψ`.
- `canonicalPullback_reindex Φ R p ψ hψ M n`: the pullback along the
  reindexed tower morphism is
  `Functor.whiskerLeft Φ.functor.op (canonicalPullback R p ψ hψ M n)`, by
  `rfl`.
- `canonicalPullback_reindexComparison Φ R p ψ hψ M n`: the comparisons for
  `canonicalCoefficients R p M` and `canonicalCoefficients R p' M` intertwine
  the colimit maps of these two pullbacks. This is the published
  `map_reindexComparison`.

## Base change and the Galois action

Let `F` and `L` be commutative rings with `Algebra F L`, and let
`s : T ⟶ (Functor.const (CompactOpenLevel G)).obj (Spec F)` be structure maps.

- `baseChangeTower_reindex Φ F L s`: the base change of the reindexed tower,
  with structure maps `reindexProjection Φ s`, is
  `Φ.functor ⋙ baseChangeTower F L s`, by `rfl`.
- `towerGaloisAction_reindex Φ F L s σ`: for `σ : L ≃ₐ[F] L`, the Galois
  automorphism of the reindexed base-changed tower is the whiskering by
  `Φ.functor` of that of the base-changed tower, by `rfl`.
- `baseChangeProjection_reindex Φ F L s p`: for projections `p` of `T` to
  `X`, `baseChangeProjection F L (reindexProjection Φ s) ≫ reindexProjection Φ p`
  is `reindexProjection Φ (baseChangeProjection F L s ≫ p)`, by `rfl`.

Assume moreover that the level maps of `T` are étale, that `H` and `G` are
topological groups, that `R` is a commutative ring, and that `hT` states that
`T.map (selfArrow U k hk)` is the identity for every level `U` and `k ∈ U`.

- `reindexGaloisCohomologyFunctor Φ F L s p R hT n` is the published
  `galoisCohomologyFunctor` of the reindexed tower, with structure maps
  `reindexProjection Φ s`, projections `reindexProjection Φ p` and the
  level-triviality hypothesis `reindex_selfArrow Φ hT`. It is a functor from
  module sheaves on `X` to `Action (SmoothRep R H) (L ≃ₐ[F] L)`. It sends `M`
  to the colimit over the levels `K` of `H` of the degree `n` cohomology of
  the base change of `T (Φ K)` with coefficients pulled back from `X`.
- `galois_reindexComparison_apply Φ F L s p R hT n M σ x`: the comparison
  `LevelColimit.reindexComparison Φ` for the coefficients pulled back along
  `baseChangeProjection F L s ≫ p` commutes with the action of every
  `σ : L ≃ₐ[F] L`. The action on the source is that of
  `reindexGaloisCohomologyFunctor` and on the target that of
  `galoisCohomologyFunctor F L s p R hT n`. The proof is
  `canonicalPullback_reindexComparison` for the Galois automorphism
  `(towerGaloisAction F L s σ).unop.hom`, which lies over `X` by
  `towerGaloisAction_over`, evaluated at `x`.

## Provenance

This is an internal assembly of the published reindexing of coefficient
diagrams, the published level-functor comparisons of colimits and their
cofinal isomorphism, the published colimit cohomology of level towers, and
the published pulled-back coefficients and Galois action. No reindexing or
equivariance statement is supplied as input. Harris (1999), Proposition 4.10
on printed p. 311, is motivation only.
