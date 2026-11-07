# Colimits over levels reindexed along cofinal level functors

This internal construction shows when restricting a presheaf on levels along a
level functor does not change its colimit. Let `φ : H →* G` be a group
homomorphism and let `Φ` be a functor of compact open levels lying over `φ`.
Call `Φ` cofinal when every compact open level `L` of `G` contains the image
level `Φ K` of some level `K` of `H`. For such `Φ` and every presheaf `F` on the
levels of `G`, the published comparison map
`colim_K F (Φ K) ⟶ colim_L F L` is an isomorphism. It intertwines translation
by `h ∈ H` with translation by `φ h`, and it is natural in `F`. The main
example is transport of levels along a topological group isomorphism
`e : G ≃ₜ* H`. Here the colimit over the levels of `G` of `K ↦ F (e K)` is the
colimit of `F`, with `G` acting through `e`.

## Motivation and scope

Proposition 4.10 on printed p. 311 of Harris (1999), *Galois properties of
cohomological automorphic forms on GL(n)*, ends with the statement that its
spectral sequences are `GG(A_f^{ℓ,p})`-equivariant as the level
`K(N)^{ℓ,p}` varies. The published `Langlands.Shimura.PartialLevelTower`
treats this situation for an abstract product group `H × H'`. The finite
adelic group in the Library is not literally such a product. A consumer
therefore first transports the level tower along a topological group
isomorphism `G ≃ₜ* H × H'`. This module shows that the transport changes
neither the colimit nor its translation action. More generally, it shows the
same for any cofinal level functor.

The module constructs no isomorphism `G ≃ₜ* H × H'` of a finite adelic group,
no Shimura variety, no cohomology and no spectral sequence. Harris's passage
is motivation only; no statement from it is formalized.

## Inputs

All declarations are in namespace `Langlands.Shimura`. The published module
`Langlands.Shimura.Levels` provides the transporter category
`CompactOpenLevel G` of compact open subgroups of a group `G` with a topology.
Its arrows `a : K ⟶ L` are elements `a.element` conjugating `K` into `L`;
arrows are equal when their elements are (`Arrow.ext`), and `inclusion h` is
the arrow with element `1` for `h : K.subgroup ≤ L.subgroup`.

The published `Langlands.Shimura.LevelColimit` provides the ordered synonym
`Ordered G`, the intersection level `inf K L`, the colimit
`LevelColimit.diagram F` with legs `LevelColimit.ι F K`, the lemmas
`map_inclusion_ι` and `hom_ext`, the translations `LevelColimit.translate F g`,
`LevelColimit.action F : Action C G` and the functor
`LevelColimit.functor G C : ((CompactOpenLevel G)ᵒᵖ ⥤ C) ⥤ Action C G`.

The published `Langlands.Shimura.PartialLevelTower` provides:

- the structure `CompactOpenLevel.FunctorOver φ` of level functors over
  `φ : H →* G`, with `le_of_le` (image levels are monotone), `map_inclusion`,
  `FunctorOver.id E` over the identity and `FunctorOver.comp` over composite
  homomorphisms;
- the restriction `LevelColimit.reindex Φ F = Φ.functor.op ⋙ F` and the
  restriction functor `reindexFunctor C Φ`;
- the comparison `reindexComparison Φ F : colimit (diagram (reindex Φ F)) ⟶ colimit (diagram F)`
  with `ι_reindexComparison` (its leg at `K` is `ι F (Φ K)`),
  `map_reindexComparison` (naturality in `F`) and
  `translate_reindexComparison` (translation by `h` is intertwined with
  translation by `φ h`);
- `reindexComparisonHom Φ F`, the comparison as a morphism of objects with an
  action of `H`, and `reindexComparisonNatTrans C Φ`, the comparison maps as a
  natural transformation
  `reindexFunctor C Φ ⋙ functor H C ⟶ functor G C ⋙ Action.res C φ`.

The published `Langlands.Shimura.PEL.TraceSimilitudesLevels` provides, for
`e : G ≃ₜ* H`, the transported level `CompactOpenLevel.transport e K` (the
preimage of `K` under `e.symm`), `transport_mem`
(`e g ∈ transport e K ↔ g ∈ K`), the functor `transportFunctor e` with
`(transportFunctor e).map a` of element `e a.element`, and `transport_symm`
(`transport e.symm (transport e K) = K`).

Mathlib provides `Exists.choose`, `colimit.desc`, `colimit.ι_desc`,
`Iso.isIso_hom`, `Action.res`, `Action.mkIso`, `Action.Hom.ext` and
`NatIso.ofComponents`.

## Cofinal level functors

These declarations are in namespace
`Langlands.Shimura.CompactOpenLevel.FunctorOver`.

- `IsCofinal Φ` is the proposition that for every level `L` of `G` there is a
  level `K` of `H` with `(Φ.functor.obj K).subgroup ≤ L.subgroup`.
- `isCofinal_id E` states that the identity level functor is cofinal.
- `IsCofinal.comp` states that the composite `Φ.comp Ψ` of cofinal level
  functors is cofinal. The proof takes `M` with `Ψ M ≤ L`, then `K` with
  `Φ K ≤ M`, and applies `Ψ.le_of_le`.

## Transport of levels

These declarations are in namespace `Langlands.Shimura.CompactOpenLevel`.

- `transportOver e` is the published `transportFunctor e` as a level functor
  over `(e : G →* H)`. The element condition holds by `rfl`, and the
  membership condition is `transport_mem`. `transportOver_functor` records
  the underlying functor by `rfl`.
- `transport_transport_symm` states `transport e (transport e.symm L) = L`.
  It is `transport_symm` applied to `e.symm`.
- `isCofinal_transportOver e` states that `transportOver e` is cofinal: the
  level `transport e.symm L` of `G` has image exactly `L`.

## The comparison isomorphism

These declarations are in namespace `Langlands.Shimura.LevelColimit`. Let `C`
be a category, `Φ : FunctorOver φ` and `F : (CompactOpenLevel G)ᵒᵖ ⥤ C`.

- `map_inclusion_op_comp` states that restriction along `L ≤ M` followed by
  restriction along `K ≤ L` is restriction along `K ≤ M`. The proof uses
  `F.map_comp` and `Arrow.ext` with `1 * 1 = 1`.
- `reindex_map_inclusion_op` states that the restriction map of
  `reindex Φ F` along an inclusion `K ≤ L` is the restriction map of `F` along
  the inclusion `Φ K ≤ Φ L`. The proof is `Φ.map_inclusion`.

Assume that `C` has colimits of shape `(Ordered H)ᵒᵖ` and that `H` is a
topological group.

- `map_inclusion_ι_reindex_eq` states the following. Let `L` be a level of `G`
  and let `K` and `K'` be levels of `H` with `Φ K ≤ L` and `Φ K' ≤ L`. Then
  restricting from `L` to `Φ K` and including into the colimit of
  `reindex Φ F` at `K` agrees with the same composite for `K'`. The proof
  compares both composites with the composite through `inf K K'`, using
  `map_inclusion_ι` for `reindex Φ F`, `reindex_map_inclusion_op` and
  `map_inclusion_op_comp`.

Assume moreover that `C` has colimits of shape `(Ordered G)ᵒᵖ` and let
`hΦ : Φ.IsCofinal`.

- `cofinalLevel hΦ L` is a level of `H` chosen by `Exists.choose` from
  `hΦ L`, and `cofinalLevel_le hΦ L` states
  `(Φ.functor.obj (cofinalLevel hΦ L)).subgroup ≤ L.subgroup`.
- `cofinalCocone_naturality` states, for levels `L' ≤ L` of `G`, that
  restricting from `L` to `L'`, then to the image of `cofinalLevel hΦ L'`, and
  including at `cofinalLevel hΦ L'` equals restricting from `L` to the image
  of `cofinalLevel hΦ L` and including at `cofinalLevel hΦ L`. It follows from
  `map_inclusion_op_comp` and `map_inclusion_ι_reindex_eq`.
- `cofinalCocone F hΦ` is the cocone on `diagram F` with vertex
  `colimit (diagram (reindex Φ F))` whose leg at `L` is
  `F.map (inclusion (cofinalLevel_le hΦ L)).op ≫ ι (reindex Φ F) (cofinalLevel hΦ L)`.
  Its naturality is `cofinalCocone_naturality`.
- `reindexComparisonInv F hΦ` is the map
  `colimit (diagram F) ⟶ colimit (diagram (reindex Φ F))` given by this
  cocone, and `ι_reindexComparisonInv` states its value on each leg.
- `reindexColimitIso F hΦ : colimit (diagram (reindex Φ F)) ≅ colimit (diagram F)`
  has `hom := reindexComparison Φ F` and `inv := reindexComparisonInv F hΦ`;
  the `@[simps]` lemmas record both. The composite `hom ≫ inv` is checked on
  the legs `ι (reindex Φ F) K` by `hom_ext`. On such a leg it is restriction
  from `Φ K` to the image of `cofinalLevel hΦ (Φ K)` followed by inclusion
  there. By `map_inclusion_ι_reindex_eq` this equals restriction from `Φ K`
  to itself followed by inclusion at `K`, which is that inclusion by
  `reindex_map_inclusion_op` and `map_inclusion_ι`. The composite `inv ≫ hom`
  is checked on the legs `ι F L` by `hom_ext`, `ι_reindexComparison` and
  `map_inclusion_ι`.
- `isIso_reindexComparison F hΦ` states that `reindexComparison Φ F` is an
  isomorphism.

Assume moreover that `G` is a topological group.

- `reindexActionIso F hΦ : action (reindex Φ F) ≅ (Action.res C φ).obj (action F)`
  is `reindexColimitIso F hΦ` as an isomorphism of objects with an action of
  `H`, where `H` acts on the colimit of `F` through `φ`. It is built by
  `Action.mkIso` from `translate_reindexComparison`. `reindexActionIso_hom`
  states that its forward morphism is `reindexComparisonHom Φ F`.
- `reindexNatIso C hΦ : reindexFunctor C Φ ⋙ functor H C ≅ functor G C ⋙ Action.res C φ`
  has components `reindexActionIso F hΦ`, and its naturality is
  `map_reindexComparison`. `reindexNatIso_hom` states that its forward
  natural transformation is `reindexComparisonNatTrans C Φ`.

## Transport of colimits

Let `G` and `H` be topological groups, let `C` have colimits of shapes
`(Ordered G)ᵒᵖ` and `(Ordered H)ᵒᵖ`, let `e : G ≃ₜ* H` and let
`F : (CompactOpenLevel H)ᵒᵖ ⥤ C`.

- `transportColimitIso e F : colimit (diagram (reindex (transportOver e) F)) ≅ colimit (diagram F)`
  is `reindexColimitIso` for `isCofinal_transportOver e`.
  `transportColimitIso_hom` states that its forward map is
  `reindexComparison (transportOver e) F`.
- `transportActionIso e F` is the same isomorphism of objects with an action
  of `G`, where `G` acts on the colimit of `F` through `e`.
- `translate_transportColimitIso e F g` states that translation by `g ∈ G`
  followed by `(transportColimitIso e F).hom` equals
  `(transportColimitIso e F).hom` followed by translation by `e g`.
- `transportNatIso C e` is `reindexNatIso` for `isCofinal_transportOver e`, a
  natural isomorphism
  `reindexFunctor C (transportOver e) ⋙ functor G C ≅ functor H C ⋙ Action.res C (e : G →* H)`.
