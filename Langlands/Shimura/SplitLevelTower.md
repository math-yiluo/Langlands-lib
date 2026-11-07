# Level towers through a splitting of the group as a product

This internal construction applies the published product-level theory to a
group that is only isomorphic to a product. Let `G`, `H` and `H'` be groups
with topologies and let `e : G ≃ₜ* H × H'` be an isomorphism of topological
groups. The module embeds the two factors in `G` through `e`. It then forms
the levels `e⁻¹ (K₀ × K')` of `G` with one factor fixed, and the towers of a
presheaf `F` on the levels of `G` along them. Finally it identifies the
colimit of `F` with the iterated colimit `colim_{K₀} colim_{K'} F (e⁻¹ (K₀ × K'))`,
and translation by `G` with translation by the two factors.

## Motivation and scope

Proposition 4.10 on printed p. 311 of Harris (1999), *Galois properties of
cohomological automorphic forms on GL(n)*, ends with the statement that its
spectral sequences are `GG(A_f^{ℓ,p})`-equivariant as the level
`K(N)^{ℓ,p}` varies. There the level is a product of a component at the
places `ℓ, p` and a component away from them. The published
`Langlands.Shimura.ProductLevelColimit` treats this for an abstract product
group `H × H'`. The published `Langlands.Shimura.CofinalLevelReindex`
transports level towers along a topological group isomorphism. This module
combines the two for an arbitrary given splitting `e : G ≃ₜ* H × H'`.

The module constructs no splitting of a finite adelic group, no Shimura
variety, no cohomology and no spectral sequence. Harris's passage is
motivation only; no statement from it is formalized.

## Inputs

All declarations are in namespace `Langlands.Shimura`.

The published `Langlands.Shimura.Levels` provides the transporter category
`CompactOpenLevel G` of compact open subgroups of `G`. Its arrows `a : K ⟶ L`
have elements `a.element` conjugating `K` into `L`.

The published `Langlands.Shimura.LevelColimit` provides the ordered synonym
`Ordered G`, the colimit `LevelColimit.diagram F` with legs
`LevelColimit.ι F K`, the lemma `hom_ext`, the translations
`LevelColimit.translate F g` with `translate_mul`, the object
`LevelColimit.action F : Action C G`, the predicate `IsLevelTrivial F` (for
`k ∈ K`, the self-arrow of `K` with element `k` acts as the identity on
`F (K)`), and for level-trivial presheaves of
`R`-modules the smooth representation `smoothRep F hF`.

The published `Langlands.Shimura.PartialLevelTower` provides:

- level functors `CompactOpenLevel.FunctorOver φ` over `φ : H →* G` and their
  composite `FunctorOver.comp`;
- the product level `CompactOpenLevel.prod K K'` with subgroup
  `K × K'`, and the level functors `withLeft K₀` (the levels `K₀ × K'`, over
  `MonoidHom.inr H H'`) and `withRight K₀'` (the levels `K × K₀'`, over
  `MonoidHom.inl H H'`);
- the restriction `reindex Φ F = Φ.functor.op ⋙ F`, the restriction functor
  `reindexFunctor C Φ`, `isLevelTrivial_reindex`, the comparison
  `reindexComparison Φ F` with `ι_reindexComparison` (its leg at `K` is
  `ι F (Φ K)`) and `translate_reindexComparison` (translation by `h` is
  intertwined with translation by `φ h`), `reindexComparisonHom Φ F`, and
  `translate_reindexComparison_apply_of_mem` (if `g` lies in every image level
  `Φ K`, then translation by `g` fixes the image of the comparison of a
  level-trivial presheaf of modules);
- the partial tower `partialTower K₀ F = reindex (withLeft K₀) F` of a presheaf
  `F` on the levels of `H × H'`, and the presheaf of partial colimits
  `partialColimitFunctor F : (CompactOpenLevel H)ᵒᵖ ⥤ Action C H'` with
  `partialColimitFunctor_map_comparison` (along `a : K₀ ⟶ K₁` the transition
  followed by the comparison at `K₀` is the comparison at `K₁` followed by
  translation by `(a.element, 1)`).

The published `Langlands.Shimura.ProductLevelColimit` provides, for a presheaf
`F` on the levels of `H × H'`: the presheaf `partialColimit F` of partial
colimits with values in `C`, the legs `ιPartial F K₀` of its colimit and
`ι₂ F K₀ K'` (with `ι₂_def`), the comparison `iteratedComparison F` with
`ιPartial_iteratedComparison` (its leg at `K₀` is
`reindexComparison (withLeft K₀) F`), the isomorphism
`iteratedColimitIso F : colimit (diagram (partialColimit F)) ≅ colimit (diagram F)`
with hom `iteratedComparison F`, the translations `iteratedTranslate F h'` by
`h' ∈ H'` on the iterated colimit and the object `iteratedAction F` of
`Action C H'`, and `translate_iteratedComparison` and
`iteratedTranslate_iteratedComparison` (the comparison intertwines translation
by `h` with translation by `(h, 1)`, and translation by `h'` with translation by
`(1, h')`).

The published `Langlands.Shimura.PEL.TraceSimilitudesLevels` provides the
transported level `CompactOpenLevel.transport e K`, the preimage of `K` under
`e.symm`. The published `Langlands.Shimura.CofinalLevelReindex` provides the
level functor `transportOver e` over `e`, and
`transportColimitIso e F : colimit (diagram (reindex (transportOver e) F)) ≅ colimit (diagram F)`
with `transportColimitIso_hom` (its hom is
`reindexComparison (transportOver e) F`).

Mathlib provides `MonoidHom.inl`, `MonoidHom.inr`, `Commute`, `Action.res`
and `Action.mkIso`.

## The two factors

These declarations are in namespace `Langlands.Shimura.CompactOpenLevel`; `e`
is explicit.

- `factorHom e : H →* G` is `h ↦ e.symm (h, 1)` and
  `awayHom e : H' →* G` is `h' ↦ e.symm (1, h')`, with the `rfl` lemmas
  `factorHom_apply` and `awayHom_apply`.
- `factorHom_mul_awayHom e g`:
  `factorHom e (e g).1 * awayHom e (e g).2 = g`.
- `factorHom_commute_awayHom e h h'`: `factorHom e h` and `awayHom e h'`
  commute.
- `awayOver e K₀ : FunctorOver (awayHom e)` is `(withLeft K₀).comp (transportOver e.symm)`,
  the levels `transport e.symm (prod K₀ K')` of `G` with the first factor fixed.
  `factorOver e K₀' : FunctorOver (factorHom e)` is
  `(withRight K₀').comp (transportOver e.symm)`, the levels
  `transport e.symm (prod K K₀')` with the second factor fixed. The `rfl`
  lemmas `awayOver_functor_obj` and `factorOver_functor_obj` record these
  objects.
- `mem_transport_symm_prod e`:
  `g ∈ transport e.symm (prod K K')` if and only if `(e g).1 ∈ K` and
  `(e g).2 ∈ K'`.
- `factorHom_mem_transport_symm_prod e K' hk`: for `k ∈ K`,
  `factorHom e k ∈ transport e.symm (prod K K')`.
  `awayHom_mem_transport_symm_prod e K hk`: for `k' ∈ K'`,
  `awayHom e k' ∈ transport e.symm (prod K K')`.

## Towers along the splitting

The remaining declarations are in namespace `Langlands.Shimura.LevelColimit`.
`F : (CompactOpenLevel G)ᵒᵖ ⥤ C` is a presheaf with values in a category `C`.

- `splitTower e F = reindex (transportOver e.symm) F`, the presheaf
  `K ↦ F (e⁻¹ K)` on the levels of `H × H'`.
- `awayTower e K₀ F = reindex (awayOver e K₀) F`, the tower
  `K' ↦ F (e⁻¹ (K₀ × K'))` on the levels of `H'`, and
  `factorTower e K₀' F = reindex (factorOver e K₀') F`, the tower
  `K ↦ F (e⁻¹ (K × K₀'))` on the levels of `H`.
- `awayTower_eq e K₀ F`: `awayTower e K₀ F = partialTower K₀ (splitTower e F)`,
  by `rfl`.
- `isLevelTrivial_splitTower`, `isLevelTrivial_awayTower` and
  `isLevelTrivial_factorTower`: the three towers of a level-trivial presheaf
  are level-trivial.
- `awayTowerFunctor e C K₀ = reindexFunctor C (awayOver e K₀)`, the away towers
  as a functor of presheaves on levels.

Assume colimits of shape `(Ordered G)ᵒᵖ`, `(Ordered H')ᵒᵖ` and
`(Ordered (H × H'))ᵒᵖ` exist in `C`, and that `G`, `H` and `H'` are
topological groups.

- `reindexComparison_awayOver e F K₀`: the comparison
  `reindexComparison (awayOver e K₀) F` from the colimit of the away tower to
  the colimit of `F` is the partial comparison
  `reindexComparison (withLeft K₀) (splitTower e F)` followed by
  `(transportColimitIso e.symm F).hom`.

## Equivariance and the iterated colimit

Assume `G`, `H` and `H'` are topological groups and colimits of shape
`(Ordered G)ᵒᵖ` and `(Ordered H')ᵒᵖ` exist in `C`.

- `awayComparison e F K₀ = reindexComparisonHom (awayOver e K₀) F`, the
  comparison as a morphism
  `action (awayTower e K₀ F) ⟶ (Action.res C (awayHom e)).obj (action F)` of
  objects with an action of `H'`.
- `translate_factorHom_comm_awayHom e F h h'`: translation by `factorHom e h`
  commutes with translation by `awayHom e h'` on the colimit of `F`.

Assume moreover that colimits of shape `(Ordered H)ᵒᵖ` and
`(Ordered (H × H'))ᵒᵖ` exist in `C`.

- `factorComparison e F K₀' = reindexComparisonHom (factorOver e K₀') F`, the
  comparison as a morphism
  `action (factorTower e K₀' F) ⟶ (Action.res C (factorHom e)).obj (action F)`
  of objects with an action of `H`.
- `splitColimitIso e F : colimit (diagram (partialColimit (splitTower e F))) ≅ colimit (diagram F)`
  is `iteratedColimitIso (splitTower e F) ≪≫ transportColimitIso e.symm F`.
  Its hom is `iteratedComparison (splitTower e F) ≫ reindexComparison (transportOver e.symm) F`
  (`splitColimitIso_hom`, by `rfl`).
- `ιPartial_splitColimitIso_hom e F K₀`: on the colimit of the away tower at
  `K₀` the hom is `reindexComparison (awayOver e K₀) F`.
- `ι₂_splitColimitIso_hom e F K₀ K'`: on `F (e⁻¹ (K₀ × K'))` the hom is the
  leg `ι F (transport e.symm (prod K₀ K'))`.
- `translate_splitColimitIso_hom e F h`: the hom intertwines translation by
  `h ∈ H` on the iterated colimit with translation by `factorHom e h`.
- `iteratedTranslate_splitColimitIso_hom e F h'`: the hom intertwines
  `iteratedTranslate (splitTower e F) h'` with translation by `awayHom e h'`.
- `splitColimitIso_conj_translate e F g`: conjugating translation by `g ∈ G`
  by the isomorphism gives `iteratedTranslate (splitTower e F) (e g).2`
  followed by translation by `(e g).1` on the iterated colimit.
- `splitColimitIsoFactor e F` is the isomorphism as an isomorphism
  `action (partialColimit (splitTower e F)) ≅ (Action.res C (factorHom e)).obj (action F)`
  in `Action C H`. `splitColimitIsoAway e F` is the isomorphism as an
  isomorphism `iteratedAction (splitTower e F) ≅ (Action.res C (awayHom e)).obj (action F)`
  in `Action C H'`.

## Varying the fixed factor

Assume `H'` is a topological group and colimits of shape `(Ordered H')ᵒᵖ`
exist in `C`.

- `awayColimitFunctor e F = partialColimitFunctor (splitTower e F)`, the
  colimits of the away towers as a presheaf
  `(CompactOpenLevel H)ᵒᵖ ⥤ Action C H'`. Its transitions are morphisms of
  objects with an action of `H'`. `awayColimitFunctor_obj e F K₀` states, by
  `rfl`, that its value at `K₀` is `action (awayTower e K₀ F)`.
- `awayColimitFunctor_map_comparison e F a`: if moreover `G` and `H` are
  topological groups and colimits of shape `(Ordered G)ᵒᵖ` and
  `(Ordered (H × H'))ᵒᵖ` exist, then for `a : K₀ ⟶ K₁` the transition
  `((awayColimitFunctor e F).map a.op).hom` followed by
  `reindexComparison (awayOver e K₀) F` equals
  `reindexComparison (awayOver e K₁) F` followed by translation by
  `factorHom e a.element`.

## Smooth representations

Assume `G`, `H` and `H'` are topological groups, `R` is a commutative ring,
and colimits of shape `(Ordered G)ᵒᵖ` and `(Ordered H')ᵒᵖ` exist in
`ModuleCat R`. Let `F` be a level-trivial presheaf of `R`-modules on the
levels of `G`.

- `awaySmoothRep e K₀ F hF : SmoothRep R H'` is
  `smoothRep (awayTower e K₀ F) (isLevelTrivial_awayTower e K₀ hF)`, the smooth
  representation of `H'` on the colimit of the away tower at `K₀`.
- `translate_awayComparison_apply_of_mem e F hF K₀ hk x`: if `H'` has a
  compact open level and `k ∈ K₀`, then translation by `factorHom e k` on the
  colimit of `F` fixes the image of `x` under
  `reindexComparison (awayOver e K₀) F`.

## Proof outline

The factor lemmas unfold `factorHom` and `awayHom` and compute in `H × H'`.
`reindexComparison_awayOver` is proved leg by leg with `hom_ext`, using
`ι_reindexComparison` for `awayOver e K₀`, `withLeft K₀` and
`transportOver e.symm`. The legs of `splitColimitIso` follow from
`ιPartial_iteratedComparison` and `reindexComparison_awayOver`. The
equivariance lemmas combine `translate_iteratedComparison` or
`iteratedTranslate_iteratedComparison` with `translate_reindexComparison` for
`transportOver e.symm`; the images `e.symm (h, 1)` and `e.symm (1, h')` are
`factorHom e h` and `awayHom e h'` by definition. The conjugation formula
writes `g = factorHom e (e g).1 * awayHom e (e g).2` and uses `translate_mul`.
`awayColimitFunctor_map_comparison` combines
`partialColimitFunctor_map_comparison` with `translate_reindexComparison` for
`transportOver e.symm`. The last lemma is
`translate_reindexComparison_apply_of_mem` for `awayOver e K₀`, with
`factorHom_mem_transport_symm_prod` as the membership hypothesis.
