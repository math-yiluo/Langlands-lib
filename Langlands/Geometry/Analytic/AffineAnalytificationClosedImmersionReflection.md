# Analytic closed immersions of affine analytifications come from surjections

Let `K` be a complete, ultrametric, nontrivially normed field and let
`f : A →ₐ[K] B` be a map of commutative `K`-algebras with finite polynomial
presentations `P` and `Q`. The main theorem
`surjective_of_closedImmersion_localizedHom` shows: if
`localizedHom K P Q f` is an analytic closed immersion (`closedImmersion` of
`AnalyticImmersion`), then `f` is surjective. The algebras lie in a common
universe, independent of that of `K`.

## Top-chart coordinates

In `ClosedImmersionReflection`, for an algebra `A` in the universe of `K`:
- `topChart A` is the top affine open of `Spec A`;
- `gammaAlgHom A : A →ₐ[K] CoordinateRing (Spec.algebraMap K A)` is the inverse
  of Mathlib's global-section isomorphism `Scheme.ΓSpecIso`; its `K`-linearity
  is `Scheme.ΓSpecIso_inv_naturality`;
- `topCoordinateMap A` composes it with restriction of sections along the
  inclusion of the top open, giving the coordinate algebra of the top chart in
  the Library's glued scheme analytification. `topCoordinateMap_bijective` and
  `topCoordinateEquiv` record that it is an isomorphism, because the inclusion
  of the top open is an isomorphism on sections (`Scheme.Hom.isIso_app`).
- `specMap_comp_algebraMap` places `Spec.map f` over `Spec K`, and
  `openCoordinateMap_comp_topCoordinateMap` shows that the restriction map of
  `Spec.map f` on top charts corresponds to `f` under the top coordinates. The
  proof uses `Scheme.Hom.resLE_comp_ι` and `Scheme.ΓSpecIso_inv_naturality`.

## Comparison with the glued scheme analytification

- `locallyOfFiniteType_specAlgebraMap`: `Spec A → Spec K` is locally of finite
  type when `A` is of finite type over `K`.
- `topChartIso` is the analytic isomorphism from the polynomial-locus
  analytification of the top chart coordinate ring to `localized K P`, induced
  by `topCoordinateEquiv A` (`isIso_localizedHom_of_algEquiv`).
- `comparisonHomeomorph K P` is the homeomorphism from the glued scheme
  analytification `SchemeAnalytification.Space K (Spec.algebraMap K A)` to
  `Space K P`. It is the inverse of the published top-chart homeomorphism
  `affineTopChartHomeomorph` followed by the point map of `topChartIso`.
  `comparisonHomeomorph_ι` computes it on the top chart as
  `baseMap` of `topCoordinateMap A`.
- `comparisonHomeomorph_analytification`: under these homeomorphisms the
  glued scheme analytification `MorphismExistence.analytification` of
  `Spec.map f` is `baseMap K P Q f`. Every point is in the top chart; the
  published `isAnalytificationMap_analytification` computes the glued map
  there. Composition of base maps (`MorphismComparison.baseMap_baseMap`) and
  `openCoordinateMap_comp_topCoordinateMap` identify the two sides.

## Proofs of the main results

`surjective_of_isClosedEmbedding_of_mono` assumes that `baseMap K P Q f` is a
closed embedding and that `Spec.map f` is a monomorphism of schemes. By the
comparison, the glued scheme analytification of `Spec.map f` is a closed
embedding conjugated by homeomorphisms, hence a proper map. The morphism
`Spec.map f` is affine, so separated and quasi-compact; it is locally of
finite type because `f` is of finite type; and it is locally quasi-finite as
a monomorphism locally of finite type. The published
`isFinite_of_isProperMap_analytification`, the affine-target properness
reflection for quasi-finite morphisms, makes `Spec.map f` finite, so `f` is a
finite ring map (`IsFinite.SpecMap_iff`). The ring map is an epimorphism by
`epi_of_mono_specMap`. Mathlib's `RingHom.surjective_of_epi_of_finite` gives
surjectivity.

`surjective_of_closedImmersion_localizedHom_of_univ` treats algebras in the
universe of `K`. An analytic closed immersion is monic (`closedImmersion.mono`)
and a closed embedding on points (`closedImmersion.isClosedEmbedding`). The
first gives a ring epimorphism by `epi_of_mono_localizedHom` and hence a
monomorphism of spectra (`mono_specMap_of_epi`); the second, with
`localizedSpaceFunctor_map_localizedHom`, says that `baseMap K P Q f` is a
closed embedding. The previous theorem applies.

`surjective_of_closedImmersion_localizedHom` treats arbitrary universes by
passing to the models of `AffineAnalytificationUniverseReduction`
(`closedImmersion_iff_model` and `surjective_iff_model`).

## Provenance

This follows the argument of Berkovich, *Spectral theory and analytic
geometry over non-Archimedean fields* (1990), Proposition 3.4.7(2), printed
p.66/PDF p.80, registered as
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`:
the analytification of `Spec(f)` is a proper monomorphism, so `Spec(f)` is a
proper monomorphism, hence a closed immersion. The Lean proof obtains
finiteness from the Library's properness reflection for quasi-finite
morphisms to an affine target, which rests on the finite form of Zariski's
Main Theorem, instead of Berkovich's Proposition 3.4.7(3). The top-chart
comparison is internal to the Library's two analytification models.
