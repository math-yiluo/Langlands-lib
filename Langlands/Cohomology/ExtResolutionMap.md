# Exact-functor Ext maps on actual injective resolutions

This is an internal comparison for actual abelian categories and the existing
Mathlib `Ext.mapExactFunctor`, `InjectiveResolution.extMk`, and project
`ExtRightDerived.extAddEquivHomology`. It introduces no alternative Ext groups.

Let `F : C ⥤ D` be additive, preserve finite limits and finite colimits, and
preserve injective objects. Let `I` be an actual injective resolution of `Y`.
The existing `DerivedComparison.mapInjectiveResolution F I` resolves `F Y`.

`extMk_mapExactFunctor` states that for every nonnegative degree `n` and
actual coefficient morphism `f : X ⟶ I.cocomplex.X n` satisfying
`f ≫ I.cocomplex.d n (n + 1) = 0`,

`(I.extMk f (n + 1) rfl hf).mapExactFunctor F`

is the `extMk` class in the mapped injective resolution with coefficient
`F.map f`. The mapped cocycle condition follows by functoriality and
preservation of zero. This theorem permits independent object and morphism
universes for `C` and `D`, and independent universes in which their Ext
groups are taken. No existence of injective resolutions for all objects is
assumed: the theorem uses the supplied `I`. Its proof installs standard
derived-category models internally, without adding a chosen-model premise.

For `resolutionHomMap` and the two homology formulas, the categories retain
independent object universes but have the same morphism universe `v`. Thus
both Hom complexes take values in the same `AddCommGrpCat.{v}`.
`resolutionHomMap F I` is the actual map of natural-indexed Hom complexes
which applies `F.mapAddHom` to every coefficient morphism:

`Hom_C(X, I.cocomplex) → Hom_D(F X, (mapInjectiveResolution F I).cocomplex)`.

Its cochain-map identity is `F.map_comp`. The definition needs no Ext
existence premise; the homology formulas assume the respective `HasExt`
instances. `extAddEquivHomology_symm_map` proves that applying this map on
homology and then the inverse Ext/resolution comparison equals applying
`Ext.mapExactFunctor` after the inverse source comparison.
`extAddEquivHomology_map` gives the equivalent forward formula. Both use
exactly the existing additive equivalences, for every nonnegative degree.

The implemented proof first checks the action on cocycles from single
complexes. The private `fromSingleMk_f_zero` computes the degree-zero
component of the shifted cochain map associated with a cocycle.
`map_fromSingle` then checks functoriality componentwise, including the
singleton and shift comparisons. The private `map_extMk_cocycle` uses the
existing generic `DerivedPlus.mapExtendIso_inv_f_comp_extendXIso` from
`CohomologyPullbackDegreeZeroProof` to identify the integer extension of the
mapped resolution. Postcomposition of cocycles identifies the mapped
coefficient with `F.map f` in that resolution.

The private `extMk_hom_aug` computes the actual derived-category morphism
of `extMk` after composition with its resolution augmentation. For
`extMk_mapExactFunctor`, cancel the shifted mapped augmentation, use the
existing `Ext.mapExactFunctor_hom` formula, and apply
`localizedMappedResolutionIso_augmentation` to the actual augmentations.
Naturality of `mapDerivedCategoryFactors` transports the mapped cocycle
through localization. Functoriality of shifted morphisms reduces the
result to `map_extMk_cocycle`. This proves agreement with the existing
exact-functor Ext map, rather than only agreement of abstract group sizes.

For the homology formulas, lift a homology class along the surjective
`homologyπ` from cycles. Naturality of `homologyπ` and the existing
`extAddEquivHomology_symm_homologyπ` express both sides by `extMk`.
Apply `extMk_mapExactFunctor`, then use `cyclesMap_i` to identify the
coefficient morphisms. The forward formula follows by injectivity of the
inverse additive equivalence.

The provenance is internal, from the actual Ext/resolution construction,
exact-functor localization, and the displayed cochain and cycle identities.
Identification of the Ext-defined homeomorphism pushforward equivalence
with right-derived abelian global sections, actual Picard obstruction
naturality, and the exact field Picard-stack atlas remain further obligations.
