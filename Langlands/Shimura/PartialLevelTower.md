# Level functors over group homomorphisms and partial level towers

This internal construction compares colimits over compact open levels of two
groups. A functor of level categories lying over a group homomorphism
`φ : H →* G` turns a presheaf `F` on the levels of `G` into a presheaf on the
levels of `H`. The colimit of the reindexed presheaf maps to the colimit of
`F`, and this map intertwines translation by `h` with translation by `φ h`.
The main example is a product group `H × H'` with the first factor of the
level fixed. For a presheaf `F` on the levels of `H × H'` and a level `K₀` of
`H`, the partial tower `K' ↦ F (K₀ × K')` has a colimit with an action of `H'`.
These partial colimits vary with `K₀` as a presheaf of objects with an
`H'`-action. Each maps `H'`-equivariantly to the colimit of `F` over all levels
of `H × H'`. For level-trivial presheaves of modules the image is fixed by
`K₀ × 1`.

## Motivation and scope

The final sentence of Proposition 4.10 on printed p. 311 of Harris (1999),
*Galois properties of cohomological automorphic forms on GL(n)*, states that
the spectral sequences of the proposition are `GG(A_f^{ℓ,p})`-equivariant as
the level `K(N)^{ℓ,p}` varies. Only the part of the level away from `ℓ` and
`p` varies there. This module provides a group-theoretic form of this
situation for a product group `H × H'`: `H` stands for the factor whose level
stays fixed and `H'` for the factor whose level varies.

The finite adelic group is not literally a product in the Library. A consumer
must first transport along a topological group isomorphism `G ≃ₜ* H × H'`.
This module does not construct that transport and does not import the published
level transport of `Langlands.Shimura.PEL.TraceSimilitudesLevels`.

The module constructs no Shimura variety, no cohomology and no spectral
sequence. It does not prove that the comparison maps are injective or that the
partial colimits recover the full colimit. It proves no cofinality of product
levels and no admissibility or finiteness. Harris's passage is motivation
only; no statement from it is formalized.

## Inputs

All declarations are in namespace `Langlands.Shimura`. The published module
`Langlands.Shimura.Levels` defines the transporter category
`CompactOpenLevel G` of compact open subgroups of a group `G` with a topology.
An arrow `a : K ⟶ L` is an element `a.element` with
`a.element⁻¹ * k * a.element ∈ L.subgroup` for every `k ∈ K.subgroup`
(`a.respects`), and arrows are equal when their elements are (`Arrow.ext`).
`inclusion h` is the arrow with element `1` for
`h : K.subgroup ≤ L.subgroup`. The published `Langlands.Shimura.LevelColimit`
provides the following:

- the ordered synonym `Ordered G` with `inclusionFunctor`;
- `selfArrow K k hk`, the arrow `K ⟶ K` with element `k ∈ K`;
- `conjLevel g K` (the level `g K g⁻¹`) and `conjArrow g K` with element `g`;
- the predicate `LevelColimit.IsLevelTrivial F`, stating that every
  `F.map (selfArrow K k hk).op` is an identity;
- the colimit `LevelColimit.diagram F` and the legs `LevelColimit.ι F K`, with
  `map_inclusion_ι`, `map_ι` and `hom_ext`;
- the translations `LevelColimit.translate F g` with `ι_translate`;
- `LevelColimit.action F : Action C G`, the induced maps `LevelColimit.map α`
  with `ι_map`, and the functor `LevelColimit.functor G C`;
- for presheaves of modules, `translate_ι_apply_of_mem` and `exists_ι_apply`.

Mathlib provides `OpenSubgroup.prod`, `Action.res C φ` (restriction of an
action along `φ`), `Functor.whiskeringLeft`, `Functor.whiskeringRight`,
`Functor.opHom` and `Functor.flip`.

## Level functors over a homomorphism

These declarations are in namespace `Langlands.Shimura.CompactOpenLevel`. Let
`φ : H →* G` be a homomorphism of groups with topologies.

- `FunctorOver φ` is a structure with a functor
  `functor : CompactOpenLevel H ⥤ CompactOpenLevel G` and two fields.
  `map_element` states that `(functor.map a).element = φ a.element` for every
  arrow `a`. `map_mem` states that `φ k ∈ (functor.obj K).subgroup` whenever
  `k ∈ K.subgroup`.
- For `Φ : FunctorOver φ`, `Φ.le_of_le` states that `Φ` preserves the
  inclusion order of levels. `Φ.map_inclusion` states that `Φ` sends
  `inclusion h` to `inclusion`. `Φ.map_selfArrow` states that `Φ` sends
  `selfArrow K k hk` to the self arrow with element `φ k`.
- `Φ.ordered : Ordered H ⥤ Ordered G` is the induced functor of ordered
  levels.
- `FunctorOver.id E` is the identity functor over `MonoidHom.id E`.
  `Φ.comp Ψ` is the composite functor over `ψ.comp φ`, and `comp_functor`
  states that its functor is `Φ.functor ⋙ Ψ.functor`.

## Product levels

For groups `H` and `H'` with topologies:

- `prod K K'` is the compact open level of `H × H'` with open subgroup
  `K.openSubgroup.prod K'.openSubgroup`. Its compactness is the compactness of
  a product of compact sets. `mem_prod` states that `x ∈ prod K K'` iff
  `x.1 ∈ K` and `x.2 ∈ K'`. `prod_mono` states that the product is monotone in
  both factors.
- `prodArrow a a' : prod K K' ⟶ prod L L'` is the arrow with element
  `(a.element, a'.element)`. `prodArrow_element` records this element by
  `rfl`. `prodArrow_id` and `prodArrow_comp` state that `prodArrow` preserves
  identities and composition.
- `prodFunctor H H' : CompactOpenLevel H ⥤ CompactOpenLevel H' ⥤ CompactOpenLevel (H × H')`
  is the product as a functor of two variables. Its value at `K` sends `K'`
  to `prod K K'` and an arrow `a'` to `prodArrow (𝟙 K) a'`. An arrow `a` gives
  the natural transformation with components `prodArrow a (𝟙 K')`. The lemmas
  `prodFunctor_obj_obj`, `prodFunctor_obj_map` and `prodFunctor_map_app`
  record these by `rfl`.
- `withLeft K₀ : FunctorOver (MonoidHom.inr H H')` has functor
  `(prodFunctor H H').obj K₀`, sending `K'` to `K₀ × K'`, over the inclusion
  `h' ↦ (1, h')`. `withRight K₀' : FunctorOver (MonoidHom.inl H H')` has
  functor `(prodFunctor H H').flip.obj K₀'`, sending `K` to `K × K₀'`, over
  `h ↦ (h, 1)`. The lemmas `withLeft_functor` and `withRight_functor` record
  their functors by `rfl`.

## Reindexed colimits

These declarations are in namespace `Langlands.Shimura.LevelColimit`. Let
`Φ : FunctorOver φ` and let `C` be a category.

- `reindex Φ F` is `Φ.functor.op ⋙ F` for a presheaf
  `F : (CompactOpenLevel G)ᵒᵖ ⥤ C`. `reindexFunctor C Φ` is the same
  restriction as a functor of presheaves, via `Functor.whiskeringLeft`.
- `isLevelTrivial_reindex` states that `reindex Φ F` is level-trivial when `F`
  is. The proof uses `Φ.map_selfArrow`.

Assume now that `C` has colimits of shapes `(Ordered H)ᵒᵖ` and `(Ordered G)ᵒᵖ`.

- `map_reindex_inclusion_ι` states
  `F.map (Φ.functor.map (inclusion h)).op ≫ ι F (Φ K) = ι F (Φ L)`.
- `reindexCocone Φ F` is the cocone on the reindexed diagram with vertex
  `colimit (diagram F)` and level-`K` leg `ι F (Φ K)`. Its naturality is
  `map_reindex_inclusion_ι`.
- `reindexComparison Φ F : colimit (diagram (reindex Φ F)) ⟶ colimit (diagram F)`
  is the map out of the colimit given by this cocone. `ι_reindexComparison`
  states `ι (reindex Φ F) K ≫ reindexComparison Φ F = ι F (Φ K)`.
- `map_reindexComparison` states that the comparison is natural in `F`. For
  `α : F ⟶ F'`, the induced map of reindexed colimits followed by the
  comparison for `F'` equals the comparison for `F` followed by `map α`.

For topological groups `H` and `G`:

- `translate_reindexComparison` states
  `translate (reindex Φ F) h ≫ reindexComparison Φ F = reindexComparison Φ F ≫ translate F (φ h)`.
  The proof applies `map_ι` to the image under `Φ` of `conjArrow h K`, whose
  element is `φ h` by `map_element`.
- `reindexComparisonHom Φ F : action (reindex Φ F) ⟶ (Action.res C φ).obj (action F)`
  is the comparison as a morphism of objects with an `H`-action, where `H`
  acts on the colimit of `F` through `φ`. `reindexComparisonHom_hom` records
  its underlying map.
- `reindexComparisonNatTrans C Φ : reindexFunctor C Φ ⋙ functor H C ⟶ functor G C ⋙ Action.res C φ`
  collects these morphisms into a natural transformation, by
  `map_reindexComparison`. `reindexComparisonNatTrans_app` records its
  components.

For presheaves of modules over a commutative ring `R`:

- `reindexComparison_ι_apply` is the elementwise form of
  `ι_reindexComparison`.
- `translate_reindexComparison_apply_of_mem` assumes that `F` is level-trivial
  and that the levels of `H` form a nonempty type. It states that an element
  `g` lying in every level `Φ K` fixes every element in the image of
  `reindexComparison Φ F`. The proof writes the element as `ι (reindex Φ F) K y`
  by `exists_ι_apply` and applies `translate_ι_apply_of_mem` at level `Φ K`.

## Partial towers

Let `F : (CompactOpenLevel (H × H'))ᵒᵖ ⥤ C`.

- `partialTower K₀ F` is `reindex (withLeft K₀) F`, the presheaf
  `K' ↦ F (K₀ × K')` on the levels of `H'`.
- `partialTowerFunctor F : (CompactOpenLevel H)ᵒᵖ ⥤ (CompactOpenLevel H')ᵒᵖ ⥤ C`
  is the composite of `(prodFunctor H H').op`, `Functor.opHom` and
  `(Functor.whiskeringRight _ _ C).obj F`. `partialTowerFunctor_obj` states
  that its value at `K₀` is `partialTower K₀ F`. An arrow `a : K₀ ⟶ K₁` acts by
  the maps `F.map (prodArrow a (𝟙 K')).op`, whose arrows have element
  `(a.element, 1)` (`partialTowerFunctor_map_app`).
- `partialTowerMap F a : partialTower K₁ F ⟶ partialTower K₀ F` is the map of
  `partialTowerFunctor F` at `a`, with its type stated in terms of
  `partialTower`. `partialTowerMap_app` gives its components.
- `isLevelTrivial_partialTower` states that each partial tower of a
  level-trivial `F` is level-trivial. `isLevelTrivial_partialTowerFunctor`
  states that `partialTowerFunctor F` is level-trivial as a presheaf on the
  levels of `H`. For `k ∈ K₀` its components are
  `F.map (selfArrow (K₀ × K') (k, 1) _).op`.

Assume now that `C` has colimits of shape `(Ordered H')ᵒᵖ` and that `H'` is
a topological group.

- `partialColimitFunctor F : (CompactOpenLevel H)ᵒᵖ ⥤ Action C H'` is
  `partialTowerFunctor F ⋙ functor H' C`. `partialColimitFunctor_obj` states
  that its value at `K₀` is `action (partialTower K₀ F)`.
- `isLevelTrivial_partialColimitFunctor` states that it is level-trivial when
  `F` is.

Assume moreover that `C` has colimits of shape `(Ordered (H × H'))ᵒᵖ` and that
`H` is a topological group.

- `partialComparisonHom F K₀` is `reindexComparisonHom (withLeft K₀) F`. It is
  the `H'`-equivariant morphism from the colimit of the partial tower at `K₀`
  to the colimit of `F` over all levels of `H × H'`, on which `H'` acts through
  `h' ↦ (1, h')`.
- `partialColimitFunctor_map_comparison` states, for `a : K₀ ⟶ K₁`,
  `((partialColimitFunctor F).map a.op).hom ≫ reindexComparison (withLeft K₀) F = reindexComparison (withLeft K₁) F ≫ translate F (a.element, 1)`.
  The proof checks this on each leg `K'` using `ι_map`, `partialTowerMap_app`,
  `ι_reindexComparison` and `map_ι` for `prodArrow a (𝟙 K')`.
- For presheaves of modules, `translate_partialComparison_apply_of_mem`
  assumes that `F` is level-trivial and that the levels of `H'` form a
  nonempty type. It states that `(k, 1)` fixes the image of
  `reindexComparison (withLeft K₀) F` for every `k ∈ K₀`. This is
  `translate_reindexComparison_apply_of_mem`, since `(k, 1) ∈ K₀ × K'` for
  every `K'`.
