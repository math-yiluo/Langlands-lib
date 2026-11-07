# Cohomology of level towers of schemes away from a fixed factor of the level

This internal construction specializes the reindexed tower cohomology of
`Langlands.Shimura.ReindexLevelTowerCohomology` to a splitting of the group.
Let `G`, `H` and `H'` be groups with topologies, let `e : G ≃ₜ* H × H'` be an
isomorphism of topological groups, and let `K₀` be a compact open level of
`H`. For a level tower of schemes `T : CompactOpenLevel G ⥤ Scheme.{u}`, the
schemes `T (e⁻¹ (K₀ × K'))` form a level tower of `H'`, the away tower. The
module restricts coefficients to the away tower and forms its colimit
cohomology as a smooth representation of `H'`. It compares this
`H'`-equivariantly with the colimit cohomology of `T`, varies `K₀`, and
records the compatibility with the Galois action. Finally it applies all of
this to the published splitting of the finite adelic points of a rational
algebra with involution at the places dividing a nonzero natural number `m`.
All declarations are in namespace
`Langlands.Shimura.SplitLevelTowerCohomology`.

## Motivation and scope

Proposition 4.10 on printed p. 311 of Harris (1999), *Galois properties of
cohomological automorphic forms on GL(n)*, ends with the statement that its
spectral sequences are `GG(A_f^{ℓ,p})`-equivariant as the level
`K(N)^{ℓ,p}` varies. There the component of the level at the places `ℓ, p`
is fixed and the component away from them varies. In this module the fixed
component is `K₀` and the varying one is `K'`. The colimit over `K'` of the
cohomology of `T (e⁻¹ (K₀ × K'))` carries the action of `H'`.

The module constructs no Shimura variety and no spectral sequence. The
fixed level `K₀` of each away tower is fixed in advance, and the comparison
along a change of `K₀` is the transition of the presheaf
`awayColimitCohomologyFunctor` described below. In the rational case the
places dividing `m` are the finite places of `ℚ` whose prime ideal contains
`m`; they are not identified with rational primes here. `σ` is not
identified with Harris's inner form and `σ.FiniteAdelicPoints` is not
identified with Harris's `GG(A_f)`. Harris's passage is motivation only; no
statement from it is formalized.

## Inputs

The module `Langlands.Shimura.ReindexLevelTowerCohomology`, submitted
together with this one, provides for a level functor `Φ : FunctorOver φ`:
`reindex_selfArrow`, `reindexCoefficients`, `reindexCoefficients_canonical`,
`isLevelTrivialCoefficients_reindex`, `reindexProjection`, the comparison
`colimitCohomologyComparison Φ D q` with `ι_colimitCohomologyComparison` and
`translate_colimitCohomologyComparison_apply_of_mem`, the cofinal isomorphism
`colimitCohomologyReindexIso`, `reindexGaloisCohomologyFunctor` and
`galois_reindexComparison_apply`.

The published `Langlands.Shimura.SplitLevelTower` provides, in namespace
`Langlands.Shimura.CompactOpenLevel`, the homomorphisms
`factorHom e : H →* G` (`h ↦ e.symm (h, 1)`) and `awayHom e : H' →* G`
(`h' ↦ e.symm (1, h')`) and the level functor
`awayOver e K₀ : FunctorOver (awayHom e)` with levels
`transport e.symm (prod K₀ K')`. In namespace `Langlands.Shimura.LevelColimit`
it provides, for a presheaf `F` on the levels of `G`: the split presheaf
`splitTower e F` on the levels of `H × H'`, the away tower
`awayTower e K₀ F = reindex (awayOver e K₀) F`, the comparison
`awayComparison e F K₀ = reindexComparisonHom (awayOver e K₀) F`, the smooth
representation `awaySmoothRep e K₀ F hF`, the lemma
`translate_awayComparison_apply_of_mem` (for a level-trivial presheaf of
modules, a nonempty type of levels of `H'` and `k ∈ K₀`, translation by
`factorHom e k` fixes the image of the comparison at `K₀`), the presheaf
`awayColimitFunctor e F : (CompactOpenLevel H)ᵒᵖ ⥤ Action C H'` with
`awayColimitFunctor_map_comparison`, and the isomorphisms
`splitColimitIsoAway e F` in `Action C H'` and `splitColimitIsoFactor e F` in
`Action C H` from the iterated colimit over `K₀` and `K'` to the colimit of
`F`.

The published `Langlands.Shimura.LevelTowerCohomology` provides the
coefficient diagrams `CoefficientDiagram R T.op`, their cohomology presheaves
`D.cohomology q`, `IsLevelTrivialCoefficients`, `isLevelTrivial_cohomology`,
`colimitCohomology D q` and `smoothColimitCohomology D hD q`. The published
`Langlands.Shimura.LevelTowerCanonicalCoefficients` provides
`canonicalCoefficients R p M`, and the published
`Langlands.Shimura.LevelTowerGalois` provides `baseChangeProjection` and
`galoisCohomologyFunctor`. The published `Langlands.Shimura.PartialLevelTower`
provides `LevelColimit.reindexComparison`, and the published
`Langlands.Shimura.ProductLevelColimit` provides `LevelColimit.partialColimit`
and `LevelColimit.iteratedAction`.

The published `Langlands.Shimura.Unitary.PointsSplit` provides, for a
`ℚ`-algebra `A` with `[Ring A]` and `[Module.Finite ℚ A]`,
`σ : AlgebraInvolution ℚ A`, a natural number `m` and `hm : m ≠ 0`, the
groups `σ.DividingPoints m` (points over the product of the completions at
the finite places whose prime ideal contains `m`) and `σ.PrimeToPoints m`
(points over the prime-to-`m` finite adeles), and the isomorphism of
topological groups
`σ.finiteAdelicPointsSplit m hm : σ.FiniteAdelicPoints ≃ₜ* σ.DividingPoints m × σ.PrimeToPoints m`.

## The away tower and its coefficients

Let `T : CompactOpenLevel G ⥤ Scheme.{u}` and let `R` be a commutative ring.

- `awayLevelTower e K₀ T` is `(awayOver e K₀).functor ⋙ T`, the tower
  `K' ↦ T (e⁻¹ (K₀ × K'))` on the levels of `H'`.
- `awayLevelTower_selfArrow e K₀ hT K' k hk`: if `T.map (selfArrow K k hk)` is
  the identity for every level `K` of `G` and `k ∈ K`, the same holds for the
  away tower. It is `reindex_selfArrow (awayOver e K₀) hT`.

Assume moreover that the level maps of `T` are étale.

- `awayCoefficients e K₀ D` is `reindexCoefficients (awayOver e K₀) D`, the
  coefficients `D` restricted to the levels `e⁻¹ (K₀ × K')`.
- `awayCoefficients_cohomology e K₀ D q`: the degree `q` cohomology presheaf of
  the away coefficients is `LevelColimit.awayTower e K₀ (D.cohomology q)`, by
  `rfl`.
- `isLevelTrivialCoefficients_away e K₀ hD`: the away coefficients of
  level-trivial coefficients are level-trivial.
- `awayCoefficients_canonical e K₀ p M`: for projections `p` of `T` to a
  scheme `X` and a module sheaf `M` on `X`, the away coefficients of
  `canonicalCoefficients R p M` are
  `canonicalCoefficients R (reindexProjection (awayOver e K₀) p) M`.

## Away colimit cohomology

Assume moreover that `G`, `H` and `H'` are topological groups.

- `awayColimitCohomology e K₀ D q : Action (ModuleCat R) H'` is
  `colimitCohomology (awayCoefficients e K₀ D) q`. It is the colimit over the
  levels `K'` of `H'` of the degree `q` cohomology of `T (e⁻¹ (K₀ × K'))`,
  with the action of `H'`. `awayColimitCohomology_eq` states, by `rfl`, that
  it is `LevelColimit.action (LevelColimit.awayTower e K₀ (D.cohomology q))`.
- `smoothAwayColimitCohomology e K₀ D hD q : SmoothRep R H'` is the smooth
  representation of `H'` on the away colimit cohomology of level-trivial
  coefficients. `smoothAwayColimitCohomology_eq` states, by `rfl`, that it is
  `LevelColimit.awaySmoothRep e K₀ (D.cohomology q) (isLevelTrivial_cohomology hD q)`.
- `awayCohomologyComparison e K₀ D q` is
  `colimitCohomologyComparison (awayOver e K₀) D q`, a morphism
  `awayColimitCohomology e K₀ D q ⟶ (Action.res (ModuleCat R) (awayHom e)).obj (colimitCohomology D q)`
  of objects with an action of `H'`. `awayCohomologyComparison_eq` states, by
  `rfl`, that it is `LevelColimit.awayComparison e (D.cohomology q) K₀`.
- `ι_awayCohomologyComparison e K₀ D q K'`: on the classes of level `K'` the
  comparison is the colimit leg at level `transport e.symm (prod K₀ K')`.
- `translate_awayCohomologyComparison_apply_of_mem e K₀ hD q hk x`: assume
  that `D` is level-trivial, that `H'` has a compact open level and that
  `k ∈ K₀`. Then `factorHom e k` acting on `colimitCohomology D q` fixes the
  image of `x` under the comparison at `K₀`. This is the published
  `translate_awayComparison_apply_of_mem`.
- `awayCohomologyIso e hK₀ D q`: if `awayOver e K₀` is cofinal, the comparison
  at `K₀` is an isomorphism of objects with an action of `H'`. It is
  `colimitCohomologyReindexIso hK₀ D q`, and `awayCohomologyIso_hom` states
  that its forward morphism is `awayCohomologyComparison e K₀ D q`.

## Varying the fixed level

- `awayColimitCohomologyFunctor e D q : (CompactOpenLevel H)ᵒᵖ ⥤ Action (ModuleCat R) H'`
  is `LevelColimit.awayColimitFunctor e (D.cohomology q)`.
  `awayColimitCohomologyFunctor_obj` states, by `rfl`, that its value at
  `op K₀` is `awayColimitCohomology e K₀ D q`.
- `awayColimitCohomologyFunctor_map_comparison e D q a`: for `a : K₀ ⟶ K₁`,
  the transition along `a.op` followed by the comparison at `K₀` equals the
  comparison at `K₁` followed by the action of `factorHom e a.element` on
  `colimitCohomology D q`. This is the published
  `awayColimitFunctor_map_comparison`.
- `splitCohomologyIsoAway e D q` is the published
  `LevelColimit.splitColimitIsoAway e (D.cohomology q)`, an isomorphism
  `LevelColimit.iteratedAction (LevelColimit.splitTower e (D.cohomology q)) ≅ (Action.res (ModuleCat R) (awayHom e)).obj (colimitCohomology D q)`
  in `Action (ModuleCat R) H'`. Thus the colimit cohomology of `T` is the
  colimit over the levels `K₀` of `H` of the colimits over `K'` of the
  cohomology of `T (e⁻¹ (K₀ × K'))`, with `H'` acting through `awayHom e`.
- `splitCohomologyIsoFactor e D q` is the published
  `LevelColimit.splitColimitIsoFactor e (D.cohomology q)`, the same
  isomorphism in `Action (ModuleCat R) H`, from
  `LevelColimit.action (LevelColimit.partialColimit (LevelColimit.splitTower e (D.cohomology q)))`
  to the colimit cohomology of `T` with `H` acting through `factorHom e`.
  `splitCohomologyIsoAway_hom_hom` states, by `rfl`, that the two
  isomorphisms have the same underlying map.

## Base change and the Galois action

Let `F` and `L` be commutative rings with `Algebra F L`, let `s` be structure
maps of `T` to `Spec F`, let `p` be projections of `T` to a scheme `X`, and
let `hT` state that every `T.map (selfArrow K k hk)` with `k ∈ K` is the
identity.

- `awayGaloisCohomologyFunctor e K₀ F L s p R hT n` is
  `reindexGaloisCohomologyFunctor (awayOver e K₀) F L s p R hT n`, a functor
  from module sheaves on `X` to `Action (SmoothRep R H') (L ≃ₐ[F] L)`. It
  sends `M` to the colimit over the levels `K'` of `H'` of the degree `n`
  cohomology of the base change to `Spec L` of `T (e⁻¹ (K₀ × K'))`, with
  coefficients pulled back from `X`.
- `galois_awayComparison_apply e K₀ F L s p R hT n M σ x`: the comparison
  `LevelColimit.reindexComparison (awayOver e K₀)` for the coefficients pulled
  back along `baseChangeProjection F L s ≫ p` commutes with the action of
  every `σ : L ≃ₐ[F] L`, on the source through
  `awayGaloisCohomologyFunctor` and on the target through
  `galoisCohomologyFunctor F L s p R hT n`. It is
  `galois_reindexComparison_apply (awayOver e K₀)`.

## Away from the places dividing an integer

Let `A`, `σ`, `m` and `hm` be as in the inputs, let `K₀` be a compact open
level of `σ.DividingPoints m`, and let
`T : CompactOpenLevel σ.FiniteAdelicPoints ⥤ Scheme.{u}` have étale level
maps. Write `e = σ.finiteAdelicPointsSplit m hm`.

- `primeToSchemeTower σ m hm K₀ T` is `awayLevelTower e K₀ T`, the tower
  `K' ↦ T (e⁻¹ (K₀ × K'))` on the levels of `σ.PrimeToPoints m`.
- `primeToColimitCohomology σ m hm K₀ D q` is
  `awayColimitCohomology e K₀ D q`, an object of
  `Action (ModuleCat R) (σ.PrimeToPoints m)`.
- `smoothPrimeToColimitCohomology σ m hm K₀ D hD q` is
  `smoothAwayColimitCohomology e K₀ D hD q`, a smooth representation of
  `σ.PrimeToPoints m` for level-trivial `D`.
- `primeToCohomologyComparison σ m hm K₀ D q` is
  `awayCohomologyComparison e K₀ D q`, equivariant for `σ.PrimeToPoints m`
  acting on the colimit cohomology of `T` through `awayHom e`.
- `primeToColimitCohomologyFunctor σ m hm D q` is
  `awayColimitCohomologyFunctor e D q`, the presheaf on the levels `K₀` of
  `σ.DividingPoints m`.
- `primeToSplitCohomologyIso σ m hm D q` is `splitCohomologyIsoAway e D q`:
  the colimit cohomology of `T` is the colimit over the levels `K₀` of
  `σ.DividingPoints m` of the prime-to-`m` colimit cohomology, equivariantly
  for `σ.PrimeToPoints m`.

## Proof outline

Every declaration is a specialization. The away declarations apply the
declarations of `ReindexLevelTowerCohomology` to `Φ = awayOver e K₀`. The
equalities with the published away constructions of `SplitLevelTower` hold
by `rfl`, because `awayTower`, `awayComparison` and `awaySmoothRep` are
defined as the corresponding reindexed constructions for `awayOver e K₀`.
`translate_awayCohomologyComparison_apply_of_mem`,
`awayColimitCohomologyFunctor_map_comparison`, `splitCohomologyIsoAway` and
`splitCohomologyIsoFactor` are the published lemmas and isomorphisms of
`SplitLevelTower` for the presheaf `D.cohomology q`, with
`isLevelTrivial_cohomology` where level triviality is needed. The prime-to-`m`
declarations take `e = σ.finiteAdelicPointsSplit m hm`.

## Provenance

This is an internal specialization of the reindexed tower cohomology of
`ReindexLevelTowerCohomology` and the published away towers, comparisons and
iterated colimit isomorphisms of `SplitLevelTower`, applied to the published
splitting `finiteAdelicPointsSplit` of `PointsSplit`. No equivariance or
isomorphism statement is supplied as input. Harris (1999), Proposition 4.10
on printed p. 311, is motivation only.
