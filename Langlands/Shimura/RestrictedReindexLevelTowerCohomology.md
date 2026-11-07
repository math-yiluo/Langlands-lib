# Towers of schemes over levels satisfying a property, reindexed along level functors

This internal construction repeats the published reindexed tower cohomology
(`Langlands.Shimura.ReindexLevelTowerCohomology`) for towers of schemes
defined only over the levels satisfying a property. Let `H` and `G` be groups
with topologies, let `φ : H →* G` be a group homomorphism, let
`Φ : FunctorOver φ` be a level functor over `φ`, and let `P` and `P'` be
properties of the compact open levels of `G` and of `H`. Let
`hΦ : ∀ K, P' K → P (Φ.functor.obj K)`. A tower
`T : P.FullSubcategory ⥤ Scheme.{u}` then gives the reindexed tower
`Φ.restrictedFunctor hΦ ⋙ T`, with schemes `T (Φ K)` for the levels `K` of
`H` satisfying `P'`. The module shows that the hypotheses of the published
restricted tower cohomology are inherited by the reindexed tower. It compares
the colimit cohomology of the reindexed tower `H`-equivariantly with that of
`T` and identifies this comparison with the one over all levels. It also
records how reindexing interacts with pulled-back coefficients, base change
and the Galois action. All declarations are in namespace
`Langlands.Shimura.RestrictedReindexLevelTowerCohomology`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, Proposition 4.10 on printed p. 311, ends with the statement that its
spectral sequences are `GG(A_f^{ℓ,p})`-equivariant as the level
`K(N)^{ℓ,p}` varies. Shimura towers are often defined only for sufficiently
small levels, so the cohomology is a colimit over the levels satisfying a
property, and restricting to the levels with a fixed component at `ℓ, p`
reindexes such a tower. The module
`Langlands.Shimura.RestrictedSplitLevelTowerCohomology`, submitted together
with this one, applies it to a splitting of the group.

The module constructs no Shimura variety, no particular level functor, no
particular property of levels and no spectral sequence. Harris's passage is
motivation only; no statement from it is formalized.

## Inputs

The module `Langlands.Shimura.RestrictedLevelReindex`, submitted together
with this one, provides `Φ.restrictedFunctor hΦ`, its lemma
`restrictedFunctor_map_restrictedSelfArrow`, the predicate
`Φ.IsRestrictedCofinal P' P`, and, in namespace
`Langlands.Shimura.RestrictedLevelColimit`, the reindexed presheaf
`reindex Φ hΦ F`, the comparison `reindexComparison Φ hΦ F` with
`ι_reindexComparison` and `map_reindexComparison`, its equivariant form
`reindexComparisonHom Φ hΦ F`, the lemma
`translate_reindexComparison_apply_of_mem`, the isomorphism
`reindexActionIso hΦ F hc` for `hc : Φ.IsRestrictedCofinal P' P`, and the
compatibility `reindexComparisonHom_actionRestrictIso_hom` with the
comparison over all levels.

The published `Langlands.Shimura.RestrictedLevelColimit` provides
`P.FullSubcategory`, `restrictedSelfArrow P K k hk`, the classes
`IsDownwardClosed P` and `IsConjStable P`, and the colimit legs
`RestrictedLevelColimit.ι` and colimit maps `RestrictedLevelColimit.map`.

The published `Langlands.Geometry.EtaleCohomologyReindex` provides
`CoefficientDiagram.reindex F D` and `CoefficientDiagram.reindexFunctor F`
for an index functor `F`.

The published `Langlands.Shimura.RestrictedLevelTowerCohomology` provides,
in namespace `Langlands.Shimura.RestrictedLevelTowerCohomology`, for `T` with
étale level maps and a commutative ring `R`: the coefficient diagrams
`CoefficientDiagram R T.op` with cohomology presheaves `D.cohomology q` and
section presheaf `D.sections`, the predicate `IsLevelTrivialCoefficients D`
(for `k ∈ K` the self-arrow acts on `T K` by the same scheme morphism as the
identity arrow, and its coefficient map is the identity coefficient map
transported by `restrictionCongr`), the property
`levelTrivialCoefficients T R`, `isLevelTrivial_cohomology`, and for a
topological group `G` and `P` conjugation stable the colimit cohomology
`colimitCohomology D q : Action (ModuleCat R) G`. For a tower
`T₀ : CompactOpenLevel G ⥤ Scheme.{u}` over all levels it provides
`restrictCoefficients D₀` on `P.ι ⋙ T₀` and, for `P` moreover downward closed
and holding for some level, `colimitCohomologyRestrictIso D₀ q` from the
colimit cohomology of `restrictCoefficients D₀` to the published
`LevelTowerCohomology.colimitCohomology D₀ q`.

The published `Langlands.Shimura.RestrictedLevelTowerCanonicalCoefficients`
provides, in the same namespace, for projections
`p : T ⟶ (Functor.const P.FullSubcategory).obj X` to a scheme `X` and a module
sheaf `M` on `X`, the coefficients `canonicalCoefficients R p M`; for a tower
morphism `ψ : T' ⟶ T` with étale components and `hψ : ψ ≫ p = p'`, the
pullback `canonicalPullback R p ψ hψ M n`; and for projections `p₀` of a tower
over all levels, `restrictProjection P p₀`.

The published `Langlands.Shimura.RestrictedLevelTowerGalois` provides, for
structure maps `s : T ⟶ (Functor.const P.FullSubcategory).obj (Spec F)` and
an `F`-algebra `L`: `baseChangeTower F L s`, `baseChangeProjection F L s`,
`towerGaloisAction F L s`, `towerGaloisAction_over`, and the functor
`galoisCohomologyFunctor F L s p R hT n` from module sheaves on `X` to
`Action (SmoothRep R G) (L ≃ₐ[F] L)`.

The published `Langlands.Shimura.ReindexLevelTowerCohomology` provides, for a
tower `T₀` over all levels, `ReindexLevelTowerCohomology.reindexCoefficients Φ D₀`,
`ReindexLevelTowerCohomology.reindexProjection Φ p₀` and the comparison
`ReindexLevelTowerCohomology.colimitCohomologyComparison Φ D₀ q`.

## Reindexed towers and coefficients

Let `T : P.FullSubcategory ⥤ Scheme.{u}` and let `R` be a commutative ring.

- The instance `etale_reindex_map`: if the level maps of `T` are étale, so
  are those of `Φ.restrictedFunctor hΦ ⋙ T`.
- `reindex_selfArrow Φ hΦ hT K k hk`: if `T.map (restrictedSelfArrow P K k hk)`
  is the identity for every level `K` satisfying `P` and `k ∈ K`, the same
  holds for the reindexed tower. The proof rewrites with
  `restrictedFunctor_map_restrictedSelfArrow`.

Assume moreover that the level maps of `T` are étale.

- `reindexCoefficients Φ hΦ D` is
  `CoefficientDiagram.reindex (Φ.restrictedFunctor hΦ).op D`. The `rfl`
  lemmas `reindexCoefficients_obj` and `reindexCoefficients_map` give its
  sheaf at `K` (that of `D` at `Φ K`) and its maps.
- `reindexCoefficients_cohomology Φ hΦ D q` and
  `reindexCoefficients_sections Φ hΦ D` state, by `rfl`, that its cohomology
  and section presheaves are `RestrictedLevelColimit.reindex Φ hΦ (D.cohomology q)`
  and `RestrictedLevelColimit.reindex Φ hΦ D.sections`.
- `isLevelTrivialCoefficients_reindex Φ hΦ hD`: reindexing level-trivial
  coefficients gives level-trivial coefficients. For `k ∈ K` it applies `hD`
  at `Φ K` and `φ k` (using `Φ.map_mem`), after rewriting the self-arrow with
  `restrictedFunctor_map_restrictedSelfArrow` and the identity arrow with
  `map_id`.
- `reindexCoefficientsFunctor Φ hΦ T R` is reindexing as a functor between
  the full subcategories of level-trivial coefficient diagrams, with
  `reindexCoefficientsFunctor_obj_obj` (by `rfl`).
- `cohomologyMap_reindex Φ hΦ α q`: the cohomology map of a reindexed
  coefficient morphism is the whiskering by `(Φ.restrictedFunctor hΦ).op` of
  `cohomologyMap α q`, by `rfl`.
- `reindexCoefficients_restrict Φ hΦ D₀`: for coefficients `D₀` on a tower
  `T₀` over all levels, restricting to the levels satisfying `P` and
  reindexing gives `restrictCoefficients` for `P'` of
  `ReindexLevelTowerCohomology.reindexCoefficients Φ D₀`, by `rfl`.

## The comparison of colimit cohomology

Assume moreover that `H` and `G` are topological groups and that `P` and
`P'` are conjugation stable.

- `colimitCohomologyComparison Φ hΦ D q` is
  `RestrictedLevelColimit.reindexComparisonHom Φ hΦ (D.cohomology q)`, a
  morphism
  `colimitCohomology (reindexCoefficients Φ hΦ D) q ⟶ (Action.res (ModuleCat R) φ).obj (colimitCohomology D q)`
  of objects with an action of `H`. `colimitCohomologyComparison_hom` records
  its underlying map, by `rfl`.
- `ι_colimitCohomologyComparison Φ hΦ D q K`: on the classes of level `K`
  the comparison is the colimit leg at level `Φ K`.
- `map_colimitCohomologyComparison Φ hΦ α q`: the comparison is natural in
  the coefficient morphism `α : D ⟶ E`.
- `translate_colimitCohomologyComparison_apply_of_mem Φ hΦ hD q hg x`:
  assume that `P'` is downward closed and holds for some level, that `D` is
  level-trivial, and that `g ∈ G` lies in `Φ.functor.obj K.obj` for every
  level `K` satisfying `P'`. Then `g` fixes the image of every `x` under the
  comparison. This is `translate_reindexComparison_apply_of_mem` with
  `isLevelTrivial_cohomology hD q`.
- `colimitCohomologyReindexIso hc D q`: if `P'` is downward closed and
  `hc : Φ.IsRestrictedCofinal P' P`, the comparison is an isomorphism of
  objects with an action of `H`. It is
  `RestrictedLevelColimit.reindexActionIso hΦ (D.cohomology q) hc`, and
  `colimitCohomologyReindexIso_hom` states that its forward morphism is the
  comparison.
- `colimitCohomologyComparison_restrictIso Φ hΦ D₀ q`: assume that `P` and
  `P'` are downward closed and each holds for some level, and let `D₀` be
  coefficients on a tower `T₀` over all levels with étale level maps. Then
  the comparison for `restrictCoefficients D₀` followed by
  `colimitCohomologyRestrictIso D₀ q` (with `H` acting through `φ`) equals
  `colimitCohomologyRestrictIso` for `P'` and
  `ReindexLevelTowerCohomology.reindexCoefficients Φ D₀`, followed by
  `ReindexLevelTowerCohomology.colimitCohomologyComparison Φ D₀ q`. This is
  `reindexComparisonHom_actionRestrictIso_hom` for `D₀.cohomology q`.

## Coefficients pulled back from a base

Let `X` be a scheme and `p : T ⟶ (Functor.const P.FullSubcategory).obj X`.

- `reindexProjection Φ hΦ p` has component `p.app (Φ K)` at `K`
  (`reindexProjection_app`, by `rfl`).
- `reindexProjection_restrict Φ hΦ p₀`: for projections `p₀` of a tower over
  all levels, `reindexProjection Φ hΦ (restrictProjection P p₀)` is
  `restrictProjection P' (ReindexLevelTowerCohomology.reindexProjection Φ p₀)`,
  by `rfl`.
- `reindexCoefficients_canonical Φ hΦ R p M`: reindexing
  `canonicalCoefficients R p M` gives
  `canonicalCoefficients R (reindexProjection Φ hΦ p) M`, by `rfl`.

Let `T'` be a second tower with étale level maps, `ψ : T' ⟶ T` with étale
components, and `hψ : ψ ≫ p = p'`.

- The instance `etale_whiskerLeft_app`: the components of
  `Functor.whiskerLeft (Φ.restrictedFunctor hΦ) ψ` are étale.
- `whiskerLeft_reindexProjection Φ hΦ p ψ hψ`: the whiskered morphism lies
  over `X` through the reindexed projections, checked componentwise.
- `canonicalPullback_reindex Φ hΦ R p ψ hψ M n`: the pullback along the
  whiskered morphism is the whiskering by `(Φ.restrictedFunctor hΦ).op` of
  `canonicalPullback R p ψ hψ M n`, by `rfl`.
- `canonicalPullback_reindexComparison Φ hΦ R p ψ hψ M n`: the comparisons
  for `canonicalCoefficients R p M` and `canonicalCoefficients R p' M`
  intertwine the colimit maps of these two pullbacks. This is
  `map_reindexComparison`.

## Base change and the Galois action

Let `F` and `L` be commutative rings with `Algebra F L`, and
`s : T ⟶ (Functor.const P.FullSubcategory).obj (Spec F)`.

- `baseChangeTower_reindex Φ hΦ F L s`: the base change of the reindexed
  tower is `Φ.restrictedFunctor hΦ ⋙ baseChangeTower F L s`, by `rfl`.
- `towerGaloisAction_reindex Φ hΦ F L s σ`: the Galois automorphism of the
  reindexed base-changed tower is the whiskering of that of the base-changed
  tower, by `rfl`.
- `baseChangeProjection_reindex Φ hΦ F L s p`: the base-change projection of
  the reindexed tower followed by the reindexed projections is the
  reindexing of `baseChangeProjection F L s ≫ p`, by `rfl`.

Assume moreover that the level maps of `T` are étale, that `H` and `G` are
topological groups, that `P` and `P'` are conjugation stable, and that `hT`
states that `T.map (restrictedSelfArrow P U k hk)` is the identity for every
level `U` satisfying `P` and `k ∈ U`.

- `reindexGaloisCohomologyFunctor Φ hΦ F L s p R hT n` is the published
  `galoisCohomologyFunctor` of the reindexed tower, with structure maps
  `reindexProjection Φ hΦ s`, projections `reindexProjection Φ hΦ p` and
  `reindex_selfArrow Φ hΦ hT`. It is a functor from module sheaves on `X` to
  `Action (SmoothRep R H) (L ≃ₐ[F] L)`. It sends `M` to the colimit over the
  levels `K` satisfying `P'` of the degree `n` cohomology of the base change
  of `T (Φ K)` with coefficients pulled back from `X`.
- `galois_reindexComparison_apply Φ hΦ F L s p R hT n M σ x`: the comparison
  `RestrictedLevelColimit.reindexComparison Φ hΦ` for the coefficients
  pulled back along `baseChangeProjection F L s ≫ p` commutes with the action
  of every `σ : L ≃ₐ[F] L`. The action on the source is that of
  `reindexGaloisCohomologyFunctor` and on the target that of
  `galoisCohomologyFunctor F L s p R hT n`. The proof is
  `canonicalPullback_reindexComparison` for
  `(towerGaloisAction F L s σ).unop.hom`, which lies over `X` by
  `towerGaloisAction_over`, evaluated at `x`.

## Provenance

This is an internal assembly of the reindexed restricted colimits of
`RestrictedLevelReindex`, the published reindexing of coefficient diagrams,
the published restricted tower cohomology, pulled-back coefficients and
Galois action, and the published reindexed tower cohomology over all levels.
No reindexing or equivariance statement is supplied as input. Harris (1999),
Proposition 4.10 on printed p. 311, is motivation only.
