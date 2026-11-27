# Analytifications of étale algebra maps are étale in the localized category

`Langlands.Analytic.AffineAnalytification.affineAnalytificationLocalizedEtale` proves
`AffineAnalytificationLocalizedEtaleStatement.{u, v, w}`, in all three universes. Let `K` be a
complete ultrametric nontrivially normed field, let `A` and `B` be commutative `K`-algebras
with finite polynomial presentations `P` and `Q`, and let `f : A →ₐ[K] B` be a `K`-algebra map
whose underlying ring map is étale. Then the analytified map `localizedHom K P Q f` is étale in
the sense of `SaturatedAtlasPresentation.etale`. This is one direction of Berkovich,
*Spectral theory and analytic geometry over non-Archimedean fields* (1990),
Proposition 3.4.6(3), in the affine case.

## Proof

The proof composes three results of the Library.

1. `affineAnalytificationEtale` proves `AffineAnalytificationEtaleStatement`. Its third
   component says that `f.toRingHom.Etale` is equivalent to the finite-pieces étale predicate
   `StrongHom.IsEtale (A := presentation K Q) (B := presentation K P) (saturatedHom K P Q f)`.
   For étale `f` this gives that predicate. `StrongHom.IsEtale.isEtaleAllPieces` upgrades it to
   étaleness over all recognized pieces of the first saturations,
   `StrongHom.IsEtaleAllPieces (A := presentation K Q) (B := presentation K P)`.
2. `saturated K P` is by definition `SaturatedAtlasPresentation.ofSaturation (presentation K P)`,
   so `saturatedHom K P Q f` is a morphism `ofSaturation (presentation K Q) ⟶
   ofSaturation (presentation K P)`. `strongEtale_ofSaturation_iff_isEtaleAllPieces` holds for
   original presentations in any index universe. It identifies the canonical strong étale
   property `strongEtale` of such a morphism with étaleness over all recognized pieces of the
   original presentations. Step 1 therefore gives `strongEtale (saturatedHom K P Q f)`.
3. `localizedHom K P Q f` is by definition `localizationFunctor.map (saturatedHom K P Q f)`, and
   `etale_localizationFunctor_map_iff_strongEtale` says that the image of an actual morphism
   under `localizationFunctor` is étale exactly when the morphism is `strongEtale`.

## Universes

The presentation `presentation K P` is an `AffinoidAtlasPresentation.{u, u, 0}`: its space lies
in the universe `u` of `K` and its chart indices in `Type`, whatever the universes `v` and `w`
of `A` and `B`. Its saturation `saturated K P` is a `SaturatedAtlasPresentation.{u, u, u}`.
Step 2 is where the index universes `0` and `u` differ: `strongEtale_ofSaturation_iff` in
`SaturatedEtaleComparison` requires the index universe to be the space universe, while
`strongEtale_ofSaturation_iff_isEtaleAllPieces` in `StrongEtaleSmallIndexComparisonProof` does
not.
