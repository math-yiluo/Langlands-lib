# The actual Ext adjunction through injective resolutions

This internal construction uses actual additive functors `F : C ⥤ D` and
`G : D ⥤ C` with an actual adjunction `adj : F ⊣ G`. The abelian categories
have independent object universes and a common morphism universe `v`.
`homAdjunctionIso adj X` packages the inverse of the actual additive Hom
adjunction as a natural isomorphism

`G ⋙ Hom_C(X, -) ≅ Hom_D(F X, -)`.

This definition needs no exactness, Ext, or injective-resolution premise.
Its naturality is the published Hom-adjunction naturality in the coefficient.

For the Ext formulas, assume `F` and `G` preserve finite limits and finite
colimits, and `G` preserves injective objects. Assume Ext exists in each
category, with independently specified Ext universes. Supply an actual
injective resolution `I` of an object `Y : D`.
`extEquiv_extMk` proves that the existing `adj.extEquiv` carries the class
constructed by `I.extMk f (n + 1) rfl hf` to the class in
`mapInjectiveResolution G I` with coefficient `adj.homEquiv X _ f`.
This holds for every nonnegative degree and every coefficient morphism
satisfying the actual cocycle condition. The proof expands the published
Ext adjunction into exact-functor mapping and precomposition with the
adjunction unit. `ExtResolutionMap.extMk_mapExactFunctor` computes the
first operation, and `InjectiveResolution.mk₀_comp_extMk` computes the
second. The resulting coefficient is precisely the actual adjunct.

`adjunctionResolutionHomMap adj X I` is the actual map from the Hom complex
`Hom_D(F X, I.cocomplex)` to `Hom_C(X, (mapInjectiveResolution G I).cocomplex)`.
It is the inverse termwise cochain comparison induced by
`homAdjunctionIso`. Its components take each coefficient to its adjunct.
`extAddEquivHomology_symm_adjunction` proves that the existing Ext/resolution
comparison identifies the homology map of this actual cochain map with the
existing Ext adjunction. The proof lifts a homology class along `homologyπ`,
uses its naturality and the published cycle formula for the inverse
Ext/resolution comparison, applies `extEquiv_extMk`, and finishes with
`cyclesMap_i`. No all-object resolution-existence premise is used by these
adjunction results.

The final lemma, in the `ExtRightDerived` namespace,
`extAddEquivRightDerived_eq_of_resolution`, assumes injective resolutions
exist in `C`. It proves that the unchanged Ext/right-derived comparison at
`Y` can be computed by the Ext/Hom-homology comparison on any supplied
injective resolution `I` followed by the inverse of the canonical
`I.isoRightDerivedObj`. The proof takes an actual lift from `I` to the chosen
resolution over the identity of `Y`, applies the existing coefficient
naturality of the Ext/Hom-homology comparison, and then the canonical
derived comparison's naturality. Ext and category universes remain as stated.

The provenance is internal, from the actual Hom adjunction, exact-functor
Ext map and existing resolution comparisons. These results support the
comparison of actual Ext-defined sheaf-cohomology pushforward with derived
global sections. That cross-space comparison, actual Picard obstruction
naturality, and the exact field Picard-stack atlas remain further obligations.
