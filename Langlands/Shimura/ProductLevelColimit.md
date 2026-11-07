# Cofinality of product levels and iterated colimits over partial level towers

This internal construction shows that the colimit of a presheaf over all
compact open levels of a product group `H × H'` can be computed in two steps.
Every compact open level `K` of `H × H'` contains the product of its two
factors `{h | (h, 1) ∈ K}` and `{h' | (1, h') ∈ K}`, so product levels are
cofinal. For a presheaf `F` on the levels of `H × H'`, the colimit of `F` is
therefore isomorphic to the iterated colimit
`colim_{K₀} colim_{K'} F (K₀ × K')`. This colimit is taken first over the
levels `K'` of `H'` and then over the levels `K₀` of `H`. The isomorphism
intertwines translation by `h ∈ H` and by `h' ∈ H'` on the iterated colimit
with translation by `(h, 1)` and by `(1, h')` on the full colimit.

## Motivation and scope

The final sentence of Proposition 4.10 on printed p. 311 of Harris (1999),
*Galois properties of cohomological automorphic forms on GL(n)*, states that
the spectral sequences of the proposition are `GG(A_f^{ℓ,p})`-equivariant as
the level `K(N)^{ℓ,p}` varies. Only the part of the level away from `ℓ` and
`p` varies there. The published `Langlands.Shimura.PartialLevelTower` gives a
group-theoretic form of this situation for a product group `H × H'`, with
partial towers `K' ↦ F (K₀ × K')` in which the `H`-part `K₀` of the level is
fixed. This module shows that nothing is lost by passing to partial towers:
the colimit over the `H'`-levels of the partial tower, followed by the colimit
over `K₀`, recovers the colimit over all levels of `H × H'` with both
translation actions.

The finite adelic group is not literally a product in the Library. A consumer
must first transport along a topological group isomorphism `G ≃ₜ* H × H'`.
This module does not construct that transport. It constructs no Shimura
variety, no cohomology and no spectral sequence, and it proves no
admissibility or finiteness. Harris's passage is motivation only; no
statement from it is formalized.

## Inputs

All declarations are in namespace `Langlands.Shimura`. The published module
`Langlands.Shimura.Levels` provides the transporter category
`CompactOpenLevel G` of compact open subgroups of a group `G` with a topology.
Its arrows `a : K ⟶ L` are elements `a.element` conjugating `K` into `L`;
arrows are equal when their elements are (`Arrow.ext`), and `inclusion h` is
the arrow with element `1` for `h : K.subgroup ≤ L.subgroup`. The published
`Langlands.Shimura.LevelColimit` provides the following:

- the ordered synonym `Ordered G`, the self arrows `selfArrow K k hk` and the
  conjugation arrows `conjArrow g K : conjLevel g K ⟶ K` with element `g`,
  where `conjLevel g K` is the level `g K g⁻¹`;
- the predicate `LevelColimit.IsLevelTrivial F`;
- the colimit `LevelColimit.diagram F` with legs `LevelColimit.ι F K`, and
  the lemmas `map_inclusion_ι`, `hom_ext` and `map_ι`;
- the translations `LevelColimit.translate F g` with `translate_one`,
  `translate_mul` and `ι_translate`;
- `LevelColimit.action F : Action C G`, and the maps `LevelColimit.map α` of
  colimits induced by `α : F ⟶ F'`, with `ι_map` and `translate_map`
  (translation commutes with `map α`).

The published `Langlands.Shimura.PartialLevelTower` provides:

- `prod K K'`, the product level of `H × H'`, with `mem_prod`, `prod_mono`,
  `prodArrow a a'` (element `(a.element, a'.element)`) and `prodArrow_comp`;
- `withLeft K₀`, the level functor `K' ↦ K₀ × K'` over `h' ↦ (1, h')`;
- `reindexComparison Φ F` with `ι_reindexComparison` and
  `translate_reindexComparison`;
- the partial tower `partialTower K₀ F = K' ↦ F (K₀ × K')`, its transition
  maps `partialTowerMap F a`, `partialColimitFunctor F : (CompactOpenLevel H)ᵒᵖ ⥤ Action C H'`
  with `isLevelTrivial_partialColimitFunctor`, and
  `partialColimitFunctor_map_comparison`.

Mathlib provides `OpenSubgroup.comap`, `IsCompact.image`,
`IsCompact.of_isClosed_subset`, `OpenSubgroup.isClosed`, `colimit.desc`,
`colimit.ι_desc`, `Action.forget`, `Action.res` and `Action.mkIso`.

## Inclusions and factors of levels

These declarations are in namespace `Langlands.Shimura.CompactOpenLevel`.

- `inclusion_comp_inclusion` states that the composite of two inclusion
  arrows is the inclusion arrow. `inclusion_eq_id` states that the inclusion
  of a level in itself is the identity. Both follow from `Arrow.ext`.
- `prodArrow_inclusion` states that the product of two inclusion arrows is
  the inclusion arrow of the product levels.

Let `H` and `H'` be topological groups.

- `leftFactor K` is the compact open level of `H` with open subgroup the
  preimage of `K` under `h ↦ (h, 1)` (`OpenSubgroup.comap` along
  `MonoidHom.inl H H'`). It is compact as a closed subset of the compact image
  of `K` under the first projection. `rightFactor K` is the analogous level of
  `H'` with open subgroup the preimage under `h' ↦ (1, h')`.
  `mem_leftFactor` and `mem_rightFactor` state these memberships by `Iff.rfl`.
- `prod_leftFactor_rightFactor_le` states that
  `prod (leftFactor K) (rightFactor K) ≤ K`. The proof writes `x` as
  `(x.1, 1) * (1, x.2)`.
- `leftFactor_mono` and `rightFactor_mono` state that the factors are
  monotone in `K`.
- `le_leftFactor_prod`, `le_rightFactor_prod`, `leftFactor_prod_le` and
  `rightFactor_prod_le` state that the factors of `prod K K'` are `K` and
  `K'`, as two inclusions each.
- `exists_prod_le` states that every compact open level of `H × H'` contains a
  product level. This is the cofinality of product levels.

## The iterated colimit

These declarations are in namespace `Langlands.Shimura.LevelColimit`. Let
`C` be a category with colimits of shape `(Ordered H')ᵒᵖ`, let `H'` be a
topological group, and let `F : (CompactOpenLevel (H × H'))ᵒᵖ ⥤ C`.

- `partialColimit F` is `partialColimitFunctor F ⋙ Action.forget C H'`, the
  presheaf `K₀ ↦ colim_{K'} F (K₀ × K')` on the levels of `H` with values in
  `C`. `isLevelTrivial_partialColimit` states that it is level-trivial when
  `F` is.

Assume moreover that `C` has colimits of shape `(Ordered H)ᵒᵖ`. The iterated
colimit is `colimit (diagram (partialColimit F))`.

- `ιPartial F K₀` is the leg `ι (partialColimit F) K₀`, with its source
  stated as the colimit of the partial tower at `K₀`.
  `map_partialTowerMap_ιPartial` is `map_inclusion_ι` for this leg, and
  `ιPartial_hom_ext` is `hom_ext`.
- `ιTower F K₀ K'` is the leg `ι (partialTower K₀ F) K'`, with its source
  stated as `F.obj (op (prod K₀ K'))`. `ιTower_hom_ext` is `hom_ext` for the
  partial tower.
- `ι₂ F K₀ K'` is `ιTower F K₀ K' ≫ ιPartial F K₀`, the inclusion of level
  `K₀ × K'` into the iterated colimit; `ι₂_def` records this by `rfl`.
- `map_inclusion_ι₂` states that for `K₀ ≤ K₁` and `K' ≤ K₂` the restriction
  `F.map (inclusion (prod_mono h h')).op` followed by `ι₂ F K₀ K'` is
  `ι₂ F K₁ K₂`. The proof splits the inclusion as
  `prodArrow (inclusion h) (𝟙 K') ≫ prodArrow (𝟙 K₁) (inclusion h')` and uses
  `ι_map` for `partialTowerMap`, `map_partialTowerMap_ιPartial` and
  `map_inclusion_ι` for the partial tower at `K₁`.
- `map_inclusion_ι₂_of_le` takes `h : K₀ ≤ K₁`, `h' : K' ≤ K₂` and the
  reverse inclusion `hle : (prod K₁ K₂).subgroup ≤ (prod K₀ K').subgroup`,
  so that the two product levels have the same subgroup, and states
  `F.map (inclusion hle).op ≫ ι₂ F K₁ K₂ = ι₂ F K₀ K'`. The proof rewrites
  `ι₂ F K₁ K₂` by `map_inclusion_ι₂ F h h'` and composes the two opposite
  inclusions to the identity by `inclusion_comp_inclusion` and
  `inclusion_eq_id`. It is used in the inverse identity below, where a level
  is compared with the product of its factors.

Translation by `h' ∈ H'`:

- `partialTranslate F h' : partialColimit F ⟶ partialColimit F` is the natural
  transformation with components `translate (partialTower K₀ F) h'`. Its
  naturality is the `H'`-equivariance of the morphisms of
  `partialColimitFunctor F`.
- `iteratedTranslate F h'` is `map (partialTranslate F h')` on the iterated
  colimit. `ιPartial_iteratedTranslate` states
  `ιPartial F K₀ ≫ iteratedTranslate F h' = translate (partialTower K₀ F) h' ≫ ιPartial F K₀`.
  `iteratedTranslate_one` and `iteratedTranslate_mul` state that
  `iteratedTranslate F 1 = 𝟙 _` and
  `iteratedTranslate F (g * h) = iteratedTranslate F h ≫ iteratedTranslate F g`,
  in the order of `translate_mul`.
- `iteratedAction F : Action C H'` is the iterated colimit with this action;
  `iteratedAction_ρ` records the action.

Let `H` also be a topological group. Translation by `h ∈ H` on the iterated
colimit is the published `translate (partialColimit F) h`.

- `ιPartial_translate` is `ι_translate` for `partialColimit F`:
  `ιPartial F K₀ ≫ translate (partialColimit F) h` equals
  `map (partialTowerMap F (conjArrow h K₀)) ≫ ιPartial F (conjLevel h K₀)`.
- `translate_comm_iteratedTranslate` states that translation by `h ∈ H` and
  `iteratedTranslate F h'` commute on the iterated colimit, by
  `translate_map`.

## The comparison isomorphism

Assume moreover that `C` has colimits of shape `(Ordered (H × H'))ᵒᵖ`.

- `iteratedCocone F` is the cocone on `diagram (partialColimit F)` with vertex
  `colimit (diagram F)` and leg `reindexComparison (withLeft K₀) F` at `K₀`.
  Its naturality is `partialColimitFunctor_map_comparison` for an inclusion,
  whose element `(1, 1)` translates trivially.
- `iteratedComparison F` is the map out of the iterated colimit given by this
  cocone. `ιPartial_iteratedComparison` states that its composite with
  `ιPartial F K₀` is `reindexComparison (withLeft K₀) F`.
  `ι₂_iteratedComparison` states `ι₂ F K₀ K' ≫ iteratedComparison F = ι F (prod K₀ K')`,
  by `ι_reindexComparison`.
- `factorCocone_naturality` states, for levels `L ≤ K` of `H × H'`, that the
  restriction from `K` to `L`, then from `L` to the product of its factors,
  then `ι₂` at the factors of `L`, equals the restriction from `K` to the
  product of its factors followed by `ι₂` at the factors of `K`. The proof
  applies `map_inclusion_ι₂` to `leftFactor_mono` and `rightFactor_mono` and
  composes inclusions.
- `factorCocone F` is the cocone on `diagram F` with vertex the iterated
  colimit whose leg at `K` is
  `F.map (inclusion (prod_leftFactor_rightFactor_le K)).op ≫ ι₂ F (leftFactor K) (rightFactor K)`.
  Its naturality is `factorCocone_naturality`.
- `iteratedComparisonInv F` is the map out of `colimit (diagram F)` given by
  this cocone, and `ι_iteratedComparisonInv` states its value on each leg.
- `iteratedColimitIso F : colimit (diagram (partialColimit F)) ≅ colimit (diagram F)`
  has `hom := iteratedComparison F` and `inv := iteratedComparisonInv F`; the
  `@[simps]` lemmas record both. The composite `hom ≫ inv` is checked on the
  legs `ι₂ F K₀ K'` by `ιPartial_hom_ext` and `ιTower_hom_ext`. On such a leg
  it is the restriction from `K₀ × K'` to the product of the factors of
  `prod K₀ K'` followed by `ι₂` there. This is `ι₂ F K₀ K'` by
  `map_inclusion_ι₂_of_le`, using `le_leftFactor_prod` and
  `le_rightFactor_prod`. The composite `inv ≫ hom` is checked on the legs
  `ι F K` by `hom_ext`, `ι₂_iteratedComparison` and `map_inclusion_ι`.
- `translate_iteratedComparison` states
  `translate (partialColimit F) h ≫ iteratedComparison F = iteratedComparison F ≫ translate F (h, 1)`.
  On the leg at `K₀` it is `partialColimitFunctor_map_comparison` for
  `conjArrow h K₀`.
- `iteratedTranslate_iteratedComparison` states
  `iteratedTranslate F h' ≫ iteratedComparison F = iteratedComparison F ≫ translate F (1, h')`.
  On the leg at `K₀` it is `translate_reindexComparison` for `withLeft K₀`.
- `iteratedColimitIso_conj_translate` states that conjugating translation by
  `x ∈ H × H'` on the full colimit by `iteratedColimitIso F` gives
  `iteratedTranslate F x.2 ≫ translate (partialColimit F) x.1`. The proof
  writes `x = (x.1, 1) * (1, x.2)` and uses the two intertwining lemmas and
  `translate_mul`.
- `iteratedColimitIsoLeft F : action (partialColimit F) ≅ (Action.res C (MonoidHom.inl H H')).obj (action F)`
  is `iteratedColimitIso F` as an isomorphism of objects with an `H`-action,
  where `H` acts on the full colimit through `h ↦ (h, 1)`.
  `iteratedColimitIsoRight F : iteratedAction F ≅ (Action.res C (MonoidHom.inr H H')).obj (action F)`
  is the same isomorphism of objects with an `H'`-action, where `H'` acts
  through `h' ↦ (1, h')`. Both are built by `Action.mkIso` from the
  intertwining lemmas.
