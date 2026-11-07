# Cohomology of towers over levels satisfying a property, away from a fixed factor

This internal construction specializes the restricted reindexed tower
cohomology of `Langlands.Shimura.RestrictedReindexLevelTowerCohomology` to a
splitting of the group. It is the analogue of the published
`Langlands.Shimura.SplitLevelTowerCohomology` for towers defined only over
the levels satisfying a property. Let `G`, `H` and `H'` be groups with
topologies, let `e : G ≃ₜ* H × H'` be an isomorphism of topological groups,
let `P` be a property of the compact open levels of `G`, and let `K₀` be a
compact open level of `H`. For a tower `T : P.FullSubcategory ⥤ Scheme.{u}`,
the schemes `T (e⁻¹ (K₀ × K'))` form a tower over the levels `K'` of `H'`
for which `e⁻¹ (K₀ × K')` satisfies `P`. The module restricts coefficients to
this away tower, forms its colimit cohomology with the action of `H'`, and
compares it `H'`-equivariantly with the colimit cohomology of `T`. It also
identifies the comparison with the published one over all levels and records
the compatibility with the Galois action. Finally it applies this to the
published splitting of the finite adelic points of a rational algebra with
involution at the places dividing a nonzero natural number `m`. All
declarations are in namespace
`Langlands.Shimura.RestrictedSplitLevelTowerCohomology`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, Proposition 4.10 on printed p. 311, ends with the statement that its
spectral sequences are `GG(A_f^{ℓ,p})`-equivariant as the level
`K(N)^{ℓ,p}` varies, with the component of the level at `ℓ, p` fixed. In
this module the fixed component is `K₀` and the varying one is `K'`. The
property `P` allows towers that exist only for sufficiently small levels.

The module constructs no Shimura variety, no particular property of levels
and no spectral sequence. It does not vary `K₀`. In the rational case the
places dividing `m` are the finite places of `ℚ` whose prime ideal contains
`m`; they are not identified with rational primes here. `σ` is not
identified with Harris's inner form and `σ.FiniteAdelicPoints` is not
identified with Harris's `GG(A_f)`. Harris's passage is motivation only; no
statement from it is formalized.

## Inputs

The module `Langlands.Shimura.RestrictedLevelReindex`, submitted together
with this one, provides in namespace `Langlands.Shimura.CompactOpenLevel.FunctorOver`
for a level functor `Φ`: `Φ.restrictedFunctor hΦ`, the instances
`isDownwardClosed_inverseImage` and `isConjStable_inverseImage` for
`P.inverseImage Φ.functor`, the lemma `Φ.mapsTo_inverseImage`, and the
predicate `Φ.IsRestrictedCofinal P' P`. In namespace
`Langlands.Shimura.RestrictedLevelColimit` it provides `reindex Φ hΦ F` and
`reindexComparison Φ hΦ F`.

The module `Langlands.Shimura.RestrictedReindexLevelTowerCohomology`,
submitted together with this one, provides `reindex_selfArrow`,
`reindexCoefficients`, `isLevelTrivialCoefficients_reindex`,
`reindexProjection`, `reindexCoefficients_canonical`, the comparison
`colimitCohomologyComparison Φ hΦ D q` with `ι_colimitCohomologyComparison`,
`translate_colimitCohomologyComparison_apply_of_mem` and
`colimitCohomologyComparison_restrictIso`, the isomorphism
`colimitCohomologyReindexIso`, `reindexGaloisCohomologyFunctor` and
`galois_reindexComparison_apply`.

The published `Langlands.Shimura.SplitLevelTower` provides, in namespace
`Langlands.Shimura.CompactOpenLevel`, the homomorphisms
`factorHom e : H →* G` (`h ↦ e.symm (h, 1)`) and `awayHom e : H' →* G`
(`h' ↦ e.symm (1, h')`), the level functor
`awayOver e K₀ : FunctorOver (awayHom e)` with levels
`transport e.symm (prod K₀ K')` (`awayOver_functor_obj`), and
`factorHom_mem_transport_symm_prod` (`factorHom e k` lies in
`transport e.symm (prod K₀ K')` for `k ∈ K₀`).

The published `Langlands.Shimura.SplitLevelTowerCohomology` provides, for a
tower `T₀` over all levels of `G`, the away coefficients
`SplitLevelTowerCohomology.awayCoefficients e K₀ D₀` and the comparison
`SplitLevelTowerCohomology.awayCohomologyComparison e K₀ D₀ q`.

The published `Langlands.Shimura.RestrictedLevelTowerCohomology`,
`Langlands.Shimura.RestrictedLevelTowerCanonicalCoefficients` and
`Langlands.Shimura.RestrictedLevelTowerGalois` provide, in namespaces
`Langlands.Shimura.RestrictedLevelTowerCohomology` and
`Langlands.Shimura.RestrictedLevelTowerGalois`, the coefficient diagrams on
`T`, `IsLevelTrivialCoefficients`, `colimitCohomology`,
`smoothColimitCohomology`, `restrictCoefficients`,
`colimitCohomologyRestrictIso`, `canonicalCoefficients`,
`baseChangeProjection` and `galoisCohomologyFunctor`.

The published `Langlands.Shimura.Unitary.PointsSplit` provides, for a
`ℚ`-algebra `A` with `[Ring A]` and `[Module.Finite ℚ A]`,
`σ : AlgebraInvolution ℚ A`, a natural number `m` and `hm : m ≠ 0`, the
groups `σ.DividingPoints m` and `σ.PrimeToPoints m` and the isomorphism of
topological groups
`σ.finiteAdelicPointsSplit m hm : σ.FiniteAdelicPoints ≃ₜ* σ.DividingPoints m × σ.PrimeToPoints m`.

## The away levels

- `awayProperty e P K₀` is `P.inverseImage (awayOver e K₀).functor`, the
  property of the levels `K'` of `H'` for which `e⁻¹ (K₀ × K')` satisfies
  `P`. `awayProperty_iff e P K₀ K'` states, by `Iff.rfl`, that it holds at
  `K'` exactly when `P (transport e.symm (prod K₀ K'))`.
- `awayFunctor e P K₀` is
  `(awayOver e K₀).restrictedFunctor ((awayOver e K₀).mapsTo_inverseImage)`,
  the functor from the levels in `awayProperty e P K₀` to the levels
  satisfying `P`. `awayFunctor_obj_obj` states, by `rfl`, that it sends `K'`
  to `transport e.symm (prod K₀ K'.obj)`.

For topological groups `G` and `H'`, the instances of
`RestrictedLevelReindex` make `awayProperty e P K₀` downward closed if `P`
is, and conjugation stable if `P` is downward closed and conjugation stable.

## The away tower and its coefficients

Let `T : P.FullSubcategory ⥤ Scheme.{u}` and let `R` be a commutative ring.

- `awayLevelTower e K₀ T` is `awayFunctor e P K₀ ⋙ T`, the tower
  `K' ↦ T (e⁻¹ (K₀ × K'))` over the levels in `awayProperty e P K₀`.
- `awayLevelTower_selfArrow e K₀ hT K' k hk`: if
  `T.map (restrictedSelfArrow P K k hk)` is the identity for every level `K`
  satisfying `P` and `k ∈ K`, the same holds for the away tower. It is
  `reindex_selfArrow (awayOver e K₀)`.

Assume moreover that the level maps of `T` are étale.

- `awayCoefficients e K₀ D` is `reindexCoefficients (awayOver e K₀) _ D`, the
  coefficients `D` restricted to the levels `e⁻¹ (K₀ × K')`.
- `awayCoefficients_cohomology e K₀ D q`: its degree `q` cohomology presheaf
  is `RestrictedLevelColimit.reindex (awayOver e K₀) _ (D.cohomology q)`, by
  `rfl`.
- `isLevelTrivialCoefficients_away e K₀ hD`: the away coefficients of
  level-trivial coefficients are level-trivial.
- `awayCoefficients_canonical e K₀ p M`: for projections `p` of `T` to a
  scheme `X` and a module sheaf `M` on `X`, the away coefficients of
  `canonicalCoefficients R p M` are those pulled back along
  `reindexProjection (awayOver e K₀) _ p`.
- `awayCoefficients_restrict e K₀ D₀`: for coefficients `D₀` on a tower
  `T₀` over all levels with étale level maps, the away coefficients of
  `restrictCoefficients D₀` (for `P`) are `restrictCoefficients` for
  `awayProperty e P K₀` of `SplitLevelTowerCohomology.awayCoefficients e K₀ D₀`,
  by `rfl`.

## Away colimit cohomology

Assume moreover that `G` and `H'` are topological groups and that `P` is
downward closed and conjugation stable.

- `awayColimitCohomology e K₀ D q : Action (ModuleCat R) H'` is
  `colimitCohomology (awayCoefficients e K₀ D) q`: the colimit over the
  levels `K'` in `awayProperty e P K₀` of the degree `q` cohomology of
  `T (e⁻¹ (K₀ × K'))`, with the action of `H'`.
- `smoothAwayColimitCohomology e K₀ D hD q : SmoothRep R H'` is
  `smoothColimitCohomology` of the away coefficients, for level-trivial `D`.
- `awayCohomologyComparison e K₀ D q` is
  `colimitCohomologyComparison (awayOver e K₀) _ D q`, a morphism
  `awayColimitCohomology e K₀ D q ⟶ (Action.res (ModuleCat R) (awayHom e)).obj (colimitCohomology D q)`
  of objects with an action of `H'`.
- `ι_awayCohomologyComparison e K₀ D q K'`: on the classes of level `K'` the
  comparison is the colimit leg at level `(awayFunctor e P K₀).obj K'`.
- `translate_awayCohomologyComparison_apply_of_mem e K₀ hD q hk x`: assume
  that some level of `H'` lies in `awayProperty e P K₀`, that `D` is
  level-trivial and that `k ∈ K₀`. Then `factorHom e k` acting on
  `colimitCohomology D q` fixes the image of `x` under the comparison. It is
  `translate_colimitCohomologyComparison_apply_of_mem` with
  `factorHom_mem_transport_symm_prod`.
- `awayCohomologyIso e hK₀ D q`: if
  `hK₀ : (awayOver e K₀).IsRestrictedCofinal (awayProperty e P K₀) P`, that
  is, every level satisfying `P` contains a level `e⁻¹ (K₀ × K')` satisfying
  `P`, the comparison at `K₀` is an isomorphism of objects with an action of
  `H'`. It is `colimitCohomologyReindexIso hK₀ D q`, and
  `awayCohomologyIso_hom` states that its forward morphism is
  `awayCohomologyComparison e K₀ D q`.
- `awayCohomologyComparison_restrictIso e K₀ D₀ q`: assume that some level
  satisfies `P` and some level lies in `awayProperty e P K₀`, and let `D₀` be
  coefficients on a tower `T₀` over all levels with étale level maps. Then
  the restricted away comparison for `restrictCoefficients D₀` followed by
  `colimitCohomologyRestrictIso D₀ q` equals `colimitCohomologyRestrictIso`
  for `awayProperty e P K₀` and
  `SplitLevelTowerCohomology.awayCoefficients e K₀ D₀`, followed by the
  published away comparison
  `SplitLevelTowerCohomology.awayCohomologyComparison e K₀ D₀ q`. It is
  `colimitCohomologyComparison_restrictIso (awayOver e K₀)`.

## Base change and the Galois action

Under the same assumptions, let `F` and `L` be commutative rings with
`Algebra F L`, let `s` be structure maps of `T` to `Spec F`, let `p` be
projections of `T` to a scheme `X`, and let `hT` state that every
`T.map (restrictedSelfArrow P K k hk)` with `k ∈ K` is the identity.

- `awayGaloisCohomologyFunctor e K₀ F L s p R hT n` is
  `reindexGaloisCohomologyFunctor (awayOver e K₀) _ F L s p R hT n`, a
  functor from module sheaves on `X` to `Action (SmoothRep R H') (L ≃ₐ[F] L)`.
  It sends `M` to the colimit over the levels `K'` in `awayProperty e P K₀`
  of the degree `n` cohomology of the base change to `Spec L` of
  `T (e⁻¹ (K₀ × K'))`, with coefficients pulled back from `X`.
- `galois_awayComparison_apply e K₀ F L s p R hT n M σ x`: the comparison
  `RestrictedLevelColimit.reindexComparison (awayOver e K₀) _` for the
  coefficients pulled back along `baseChangeProjection F L s ≫ p` commutes
  with the action of every `σ : L ≃ₐ[F] L`, on the source through
  `awayGaloisCohomologyFunctor` and on the target through
  `galoisCohomologyFunctor F L s p R hT n`. It is
  `galois_reindexComparison_apply (awayOver e K₀)`.

## Away from the places dividing an integer

Let `A`, `σ`, `m` and `hm` be as in the inputs, let `K₀` be a compact open
level of `σ.DividingPoints m`, let `P` be a property of the compact open
levels of `σ.FiniteAdelicPoints`, and write `e = σ.finiteAdelicPointsSplit m hm`.

- `primeToProperty σ m hm K₀ P` is `awayProperty e P K₀`.
- `primeToSchemeTower σ m hm K₀ T` is `awayLevelTower e K₀ T` for
  `T : P.FullSubcategory ⥤ Scheme.{u}`, the tower `K' ↦ T (e⁻¹ (K₀ × K'))`
  over the levels of `σ.PrimeToPoints m` in `primeToProperty σ m hm K₀ P`.

Assume moreover that the level maps of `T` are étale and that `P` is
downward closed and conjugation stable.

- `primeToColimitCohomology σ m hm K₀ D q` is
  `awayColimitCohomology e K₀ D q`, an object of
  `Action (ModuleCat R) (σ.PrimeToPoints m)`.
- `smoothPrimeToColimitCohomology σ m hm K₀ D hD q` is
  `smoothAwayColimitCohomology e K₀ D hD q`, a smooth representation of
  `σ.PrimeToPoints m` for level-trivial `D`.
- `primeToCohomologyComparison σ m hm K₀ D q` is
  `awayCohomologyComparison e K₀ D q`, equivariant for `σ.PrimeToPoints m`
  acting on the colimit cohomology of `T` through `awayHom e`.

## Proof outline

Every declaration is a specialization of `RestrictedReindexLevelTowerCohomology`
to `Φ = awayOver e K₀`, `P' = awayProperty e P K₀` and
`hΦ = (awayOver e K₀).mapsTo_inverseImage`. The conjugation stability and
downward closure of `awayProperty e P K₀` needed for its colimit cohomology
are the instances `isConjStable_inverseImage` and
`isDownwardClosed_inverseImage`. The equalities with the published away
constructions over all levels hold by `rfl`, because
`SplitLevelTowerCohomology.awayCoefficients` is the reindexing along
`awayOver e K₀` over all levels. The prime-to-`m` declarations take
`e = σ.finiteAdelicPointsSplit m hm`.

## Provenance

This is an internal specialization of `RestrictedReindexLevelTowerCohomology`
and `RestrictedLevelReindex` to the published away level functor of
`SplitLevelTower`, compared with the published
`SplitLevelTowerCohomology`, and applied to the published splitting
`finiteAdelicPointsSplit` of `PointsSplit`. No equivariance or isomorphism
statement is supplied as input. Harris (1999), Proposition 4.10 on printed
p. 311, is motivation only.
