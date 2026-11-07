# Colimits over levels satisfying a property, reindexed along level functors

This internal construction combines two published constructions. One is the
restriction of presheaves on compact open levels along a level functor
(`Langlands.Shimura.PartialLevelTower` and
`Langlands.Shimura.CofinalLevelReindex`). The other is the group action on
colimits over the levels satisfying a property
(`Langlands.Shimura.RestrictedLevelColimit`). Let `H` and `G` be groups with
topologies, let `φ : H →* G` be a group homomorphism, let
`Φ : FunctorOver φ` be a level functor over `φ`, and let `P` and `P'` be
properties of the compact open levels of `G` and of `H`. Assume that `Φ`
sends every level satisfying `P'` to a level satisfying `P`. A presheaf `F`
on the levels satisfying `P` then restricts to a presheaf on the levels
satisfying `P'`. The module compares the colimit of the restriction with the
colimit of `F`, `H`-equivariantly for `H` acting through `φ`. It shows that
this comparison is an isomorphism when the image levels are cofinal, and
identifies it with the published comparison over all levels.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, Proposition 4.10 on printed p. 311, ends with the statement that its
spectral sequences are `GG(A_f^{ℓ,p})`-equivariant as the level
`K(N)^{ℓ,p}` varies, with the component of the level at `ℓ, p` fixed.
Shimura towers are often defined only for sufficiently small levels.
Restricting such a tower to the levels with a fixed component needs the
present reindexing of colimits over levels satisfying a property. The
modules `Langlands.Shimura.RestrictedReindexLevelTowerCohomology` and
`Langlands.Shimura.RestrictedSplitLevelTowerCohomology`, submitted together
with this one, apply it to cohomology of towers of schemes.

The module constructs no specific level functor, no specific property of
levels, no Shimura variety and no cohomology. Harris's passage is motivation
only; no statement from it is formalized.

## Inputs

All declarations are in namespace `Langlands.Shimura`.

The published `Langlands.Shimura.Levels` and `Langlands.Shimura.LevelColimit`
provide the transporter category `CompactOpenLevel G`: an arrow `a : K ⟶ L`
has an element `a.element`. They also provide `inclusion h` for
`h : K.subgroup ≤ L.subgroup`, `selfArrow K k hk` for `k ∈ K`, the
intersection `inf K L`, the conjugate level `conjLevel g K` (`g K g⁻¹`), the
arrow `conjArrow g K : conjLevel g K ⟶ K` with element `g`, and `le_conjLevel`
(the source of an arrow `a : K ⟶ L` is contained in
`conjLevel a.element L`).

The published `Langlands.Shimura.PartialLevelTower` provides level functors
`Φ : FunctorOver φ`. Such a `Φ` has an underlying functor
`Φ.functor : CompactOpenLevel H ⥤ CompactOpenLevel G`, the field
`Φ.map_element` (the image of an arrow with element `h` has element `φ h`)
and the field `Φ.map_mem` (`φ k ∈ Φ K` for `k ∈ K`). It also provides the
lemmas `Φ.le_of_le` (`Φ` is monotone in the subgroups) and `Φ.map_selfArrow`.
For presheaves `F₀` on all levels of `G` it provides
`LevelColimit.reindex Φ F₀`, the comparison
`LevelColimit.reindexComparison Φ F₀` with leg `LevelColimit.ι F₀ (Φ K)` at
`K`, and its equivariant form `LevelColimit.reindexComparisonHom Φ F₀`. The
published `Langlands.Shimura.CofinalLevelReindex` provides `Φ.IsCofinal`:
every level of `G` contains some `Φ.functor.obj K`.

The published `Langlands.Shimura.RestrictedLevelColimit` provides, for
`P : ObjectProperty (CompactOpenLevel G)`:

- the full subcategory `P.FullSubcategory` of levels satisfying `P`, the
  ordered levels `RestrictedOrdered P`, the arrows `restrictedHom P h`
  (inclusions), `restrictedSelfArrow P K k hk`, `restrictedConj P g K` and
  `restrictedConjArrow P g K`;
- the classes `IsDownwardClosed P` (every level contained in a level
  satisfying `P` satisfies `P`) and `IsConjStable P` (for a topological
  group `G`, `P K` implies `P (conjLevel g K)`);
- for `F : P.FullSubcategoryᵒᵖ ⥤ C`, the colimit `colimit (diagram F)` over
  `RestrictedOrdered P` with legs `ι F K` and `map_restrictedHom_ι`, the
  extensionality lemma `hom_ext`, translation `translate F g` with
  `ι_translate` and `map_ι`, the colimit map `map α` with `ι_map`, the object
  `action F` of `Action C G`, the functor `functor P C`, and the predicate
  `IsLevelTrivial F` (each `k ∈ K` acts on `F (op K)` as the identity);
- for presheaves of modules, `exists_ι_apply` (if `P` is downward closed and
  holds for some level, every element of the colimit comes from a single
  level) and `translate_ι_apply_of_mem` (for level-trivial `F` and `g ∈ K`,
  translation by `g` fixes the classes of level `K`);
- for `P` downward closed and holding for some level, and a presheaf `F₀` on
  all levels of `G`, the isomorphism
  `colimitRestrictIso F₀ : colimit (diagram (P.ι.op ⋙ F₀)) ≅ colimit (LevelColimit.diagram F₀)`
  with `ι_colimitRestrictIso_hom` (its leg at `K` is `LevelColimit.ι F₀ K.obj`),
  and for `P` moreover conjugation stable its equivariant form
  `actionRestrictIso F₀`.

## Levels satisfying a property

In namespace `Langlands.Shimura.CompactOpenLevel`:

- `restrictedHom_comp h₁ h₂`: inclusion arrows between levels satisfying `P`
  compose to the inclusion arrow for `h₁.trans h₂`.

In namespace `Langlands.Shimura.CompactOpenLevel.FunctorOver`, let
`hΦ : ∀ K, P' K → P (Φ.functor.obj K)`.

- `Φ.restrictedFunctor hΦ : P'.FullSubcategory ⥤ P.FullSubcategory` is the
  lift of `P'.ι ⋙ Φ.functor` through `P.ι`. The `rfl` lemmas
  `restrictedFunctor_obj_obj`, `restrictedFunctor_map_hom` and
  `restrictedFunctor_comp_ι` state that on objects it is `Φ.functor.obj`,
  on arrows `Φ.functor.map`, and that followed by `P.ι` it is
  `P'.ι ⋙ Φ.functor`.
- `restrictedFunctor_map_restrictedHom Φ hΦ h` and
  `restrictedFunctor_map_restrictedSelfArrow Φ hΦ K k hk`: it sends
  inclusion arrows to inclusion arrows and the self-arrow of `k ∈ K` to the
  self-arrow of `φ k ∈ Φ K`.
- `Φ.conjLevel_le h K`: for topological groups `H` and `G`, the image of the
  conjugate level `h K h⁻¹` is contained in `φ(h) Φ(K) φ(h)⁻¹`. It applies
  `le_conjLevel` to the image of `conjArrow h K`.
- The instance `isDownwardClosed_inverseImage`: if `P` is downward closed, so
  is `P.inverseImage Φ.functor` (the levels `K` of `H` with `P (Φ K)`), by
  `Φ.le_of_le`.
- The instance `isConjStable_inverseImage`: for topological groups `H` and
  `G`, if `P` is downward closed and conjugation stable, then so is
  `P.inverseImage Φ.functor`, by `Φ.conjLevel_le`.
- `Φ.mapsTo_inverseImage`: `Φ` sends the levels in `P.inverseImage Φ.functor`
  to levels satisfying `P`; this is the hypothesis `hΦ` for
  `P' = P.inverseImage Φ.functor`.
- `Φ.IsRestrictedCofinal P' P` is the proposition that every level `L`
  satisfying `P` contains `Φ.functor.obj K.obj` for some level `K` satisfying
  `P'`.
- `IsCofinal.isRestrictedCofinal_inverseImage hcof`: if `Φ` is cofinal and
  `P` is downward closed, `Φ.IsRestrictedCofinal (P.inverseImage Φ.functor) P`
  holds, since an image level inside a level satisfying `P` satisfies `P`.

## Reindexed presheaves and the comparison

In namespace `Langlands.Shimura.RestrictedLevelColimit`, let `C` be a
category and `F : P.FullSubcategoryᵒᵖ ⥤ C`.

- `reindex Φ hΦ F` is `(Φ.restrictedFunctor hΦ).op ⋙ F`, and
  `reindexFunctor C Φ hΦ` is restriction along `Φ.restrictedFunctor hΦ` as a
  functor of presheaf categories.
- `isLevelTrivial_reindex Φ hΦ hF`: the reindexing of a level-trivial
  presheaf is level-trivial, by `restrictedFunctor_map_restrictedSelfArrow`.
- `reindex_restrict Φ hΦ F₀`: for a presheaf `F₀` on all levels of `G`,
  `reindex Φ hΦ (P.ι.op ⋙ F₀) = P'.ι.op ⋙ LevelColimit.reindex Φ F₀`, by
  `rfl`.

Assume that `C` has colimits over `(RestrictedOrdered P')ᵒᵖ` and
`(RestrictedOrdered P)ᵒᵖ`.

- `map_reindex_restrictedHom_ι Φ hΦ F h`: for an inclusion `h` of levels
  satisfying `P'`, restricting along the image inclusion and then including
  level `Φ K` into the colimit of `F` is the inclusion of level `Φ L`.
- `reindexCocone Φ hΦ F` is the cocone on the reindexed diagram with vertex
  the colimit of `F` and leg `ι F (Φ K)` at `K`, and `reindexComparison Φ hΦ F`
  is the induced map from the colimit of `reindex Φ hΦ F` to the colimit of
  `F`. `ι_reindexComparison` states that its leg at `K` is `ι F (Φ K)`, and
  `map_reindexComparison Φ hΦ α` states naturality in `α : F ⟶ F'`.

Assume moreover that `H` and `G` are topological groups and that `P` and
`P'` are conjugation stable.

- `translate_reindexComparison Φ hΦ F h`: translation by `h ∈ H` on the
  source followed by the comparison is the comparison followed by translation
  by `φ h`. The proof applies `map_ι` to the image of
  `restrictedConjArrow P' h K` and rewrites with `Φ.map_element`.
- `reindexComparisonHom Φ hΦ F` is the comparison as a morphism
  `action (reindex Φ hΦ F) ⟶ (Action.res C φ).obj (action F)` of objects with
  an action of `H` (`reindexComparisonHom_hom`, by `rfl`).
  `reindexComparisonNatTrans C Φ hΦ` is the natural transformation
  `reindexFunctor C Φ hΦ ⋙ functor P' C ⟶ functor P C ⋙ Action.res C φ`
  with these components (`reindexComparisonNatTrans_app`, by `rfl`).

For presheaves of modules over a commutative ring `R`:

- `reindexComparison_ι_apply Φ hΦ F K x` is `ι_reindexComparison` evaluated
  at an element `x`.
- `translate_reindexComparison_apply_of_mem Φ hΦ F hF hg x`: assume that
  `G` and `H` are topological groups, `P` is conjugation stable, `P'` is
  downward closed and holds for some level, `F` is level-trivial, and `g ∈ G`
  lies in `Φ.functor.obj K.obj` for every level `K` satisfying `P'`. Then
  translation by `g` fixes the image of every `x` under the comparison. The
  proof writes `x` as a class of a single level by `exists_ι_apply` and
  applies `translate_ι_apply_of_mem`.

## Cofinal image levels

Assume that `H` is a topological group and that `P'` is downward closed.

- `map_restrictedHom_ι_reindex_eq Φ hΦ F hK hK'`: for a level `L` satisfying
  `P` and levels `K` and `K'` satisfying `P'` with `Φ K ⊆ L` and `Φ K' ⊆ L`,
  restricting from `L` to `Φ K` and including level `K` into the colimit of
  the reindexed presheaf gives the same map as doing so with `K'`. Both are
  compared with the level `inf K K'`, which satisfies `P'` because `P'` is
  downward closed.

Let `hc : Φ.IsRestrictedCofinal P' P`.

- `cofinalLevel hc L` is a level satisfying `P'` with
  `Φ (cofinalLevel hc L) ⊆ L`, chosen by `hc` (`cofinalLevel_le`).
- `cofinalCocone hΦ F hc` is the cocone on the diagram of `F` with vertex the
  colimit of the reindexed presheaf, whose leg at `L` restricts from `L` to
  `Φ (cofinalLevel hc L)` and includes level `cofinalLevel hc L`.
  `cofinalCocone_naturality` is its naturality, from `restrictedHom_comp` and
  `map_restrictedHom_ι_reindex_eq`. `reindexComparisonInv hΦ F hc` is the
  induced map, and `ι_reindexComparisonInv` describes its legs.
- `reindexColimitIso hΦ F hc` is the isomorphism with forward map
  `reindexComparison Φ hΦ F` and inverse `reindexComparisonInv hΦ F hc`, and
  `isIso_reindexComparison` states that the comparison is an isomorphism.
- For `G` a topological group and `P`, `P'` conjugation stable,
  `reindexActionIso hΦ F hc` is the same isomorphism in `Action C H` with
  forward morphism `reindexComparisonHom Φ hΦ F` (`reindexActionIso_hom`),
  and `reindexNatIso C hΦ hc` is the natural isomorphism
  `reindexFunctor C Φ hΦ ⋙ functor P' C ≅ functor P C ⋙ Action.res C φ` with
  forward morphism `reindexComparisonNatTrans C Φ hΦ` (`reindexNatIso_hom`).

## Comparison with colimits over all levels

Assume that `H` and `G` are topological groups, that `P` and `P'` are
downward closed and each holds for some level, and that `C` has colimits over
`(Ordered H)ᵒᵖ` and `(Ordered G)ᵒᵖ`. Let `F₀` be a presheaf on all levels
of `G`.

- `reindexComparison_colimitRestrictIso_hom Φ hΦ F₀`: the restricted
  comparison for `P.ι.op ⋙ F₀` followed by `colimitRestrictIso F₀` equals
  `colimitRestrictIso (LevelColimit.reindex Φ F₀)` for `P'` followed by
  the published comparison `LevelColimit.reindexComparison Φ F₀`. Both sides
  are checked on the legs of the colimit.
- `reindexComparisonHom_actionRestrictIso_hom Φ hΦ F₀`: for `P` and `P'`
  moreover conjugation stable, the same equation for the equivariant
  comparisons and `actionRestrictIso`.

## Provenance

This is an internal assembly of the published level functors and their
comparison of colimits over all levels, and of the published colimits over
levels satisfying a property with their group action and their comparison
with colimits over all levels. No reindexing, cofinality or equivariance
statement is supplied as input. Harris (1999), Proposition 4.10 on printed
p. 311, is motivation only.
