# Functoriality and presentation independence of affine analytification

The theorem
`Langlands.Analytic.AffineAnalytification.affineAnalytificationLocalizedFunctoriality`
proves the unchanged published proposition
`Langlands.Analytic.AffineAnalytification.AffineAnalytificationLocalizedFunctorialityStatement.{u, v, w, x}`.
Its module is
`Langlands.Geometry.Analytic.AffineAnalytificationLocalizedFunctorialityProof`.
The four universe parameters are independent. The field is complete,
ultrametric and nontrivially normed; the commutative algebras and algebra maps
have exactly the hypotheses of the target. Presentations may have arity zero,
and no reducedness or nonemptiness is assumed.

For presentations `P`, `P'` of `A`, `Q` of `B`, `R` of `C`, and maps
`f : A →ₐ[K] B`, `g : B →ₐ[K] C`, the theorem proves all five clauses:

1. `saturatedHom K P P (AlgHom.id K A) = 𝟙 (saturated K P)`;
2. `saturatedHom K P R (g.comp f) = saturatedHom K Q R g ≫ saturatedHom K P Q f`;
3. `localizedHom K P P (AlgHom.id K A) = 𝟙 (localized K P)`;
4. `localizedHom K P R (g.comp f) = localizedHom K Q R g ≫ localizedHom K P Q f`;
5. `IsIso (localizedHom K P P' (AlgHom.id K A))`.

The morphisms run contravariantly: the map induced by `f` has source the
analytification for `Q` and target the analytification for `P`.

## Provenance and dependencies

This module reproduces only the coordinate lemmas and strong-map
identity/composition it needs from the strong-map proof
(`AffineAnalytificationFunctorialityProof`). Those helpers occupy the separate
namespace `LocalizedFunctorialityComparison.OriginalStrongMaps`; the other
helpers occupy `LocalizedFunctorialityComparison`, both inside
`Langlands.Analytic.AffineAnalytification`. This module neither imports
`AffineAnalytificationFunctorialityProof` nor adds the separate strong-map target
theorem.

There are three imports, all from the published Library: the unchanged target
module, `DirectedAtlasComposition`, and `CompatibleStrongSaturationFunctor`.
The latter supplies the actual saturation extension's identity and composition
laws. The definitions of `saturatedHom` and `localizedHom` come from the target's
import `AffineAnalytificationLocalizedMap`.

This is a derived proof for the Library's explicit polynomial-locus model. Its
source-level provenance is that of the published statement: Berkovich 1990,
*Spectral Theory and Analytic Geometry over Non-Archimedean Fields*, Theorem
3.4.1 and Proposition 3.4.6 (printed pp.63–65/PDF pp.77–79; registered source
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`);
Berkovich 1993, *Étale cohomology for non-Archimedean analytic spaces*,
Definitions 1.2.7–1.2.9 and the category of fractions (printed pp.18–20/PDF
pp.15–17; registered `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`);
Conrad–Temkin 2009, *Non-archimedean analytification of algebraic spaces*,
Theorem 2.2.3 (printed pp.7–8; registered
`conrad-temkin-2009-nonarchimedean-analytification`, SHA256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`), as used
in Conrad 2011, *Weil and Grothendieck approaches to adelic points*, printed
p.19, final paragraph of the proof of Proposition 5.11(3) (registered
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`).
The source functoriality follows from representing properties and independence
of charts; the implemented proof computes with bounded pullbacks in the
published model.

## Strong maps on the original atlases

The helper `coordinate_eq_algebraMap` identifies each chart coordinate with the
image of the corresponding polynomial generator of `A`.
`atlas_restriction_coordinate` says restrictions preserve those coordinates.
`exists_mem_range_chart` uses the exhaustion by polydiscs and the representative
chart's equal range to show that the selected charts cover the space;
`exists_common_chart` restates the published directedness of those charts.

For a strong map into `presentation K P`, `pullback_coordinate_eq` shows that
any two admissible target charts give the same pulled-back coordinate. Pass to
a common containing target chart and use the map's restriction law and the
coordinate restriction formula. The lemma `strongHom_eq_of_coordinate` then
proves equality of strong maps from equal coordinate values, one admissible
pair per source chart for each map. Pass to a common target chart; the complete
bounded maps agree by `PresentedAffinoidAlgebra.hom_ext_coordinate`. The source
chart cover and `StrongHom.chart_comm` give equality of the continuous base
maps. Finally `StrongHom.ext_of_directed` gives equality of the entire strong
maps, including every admissible bounded pullback.

`strongHom_pullback_coordinate` computes the pullback of a generator for every
admissible pair. It reduces to the selected pair by `pullback_coordinate_eq`,
then uses `StrongHom.ofDirected_pullback_selected`, the published
`pullback_coordinate`, and `generatorValue_eq_algebraMap`.
`strongHom_pullback_algebraMap` extends this computation to every element of
`A`: precompose both algebra maps with the surjective presentation map, compare
polynomial generators using `MvPolynomial.algHom_ext`, and use surjectivity.

`strongHom_id` follows from `strongHom_eq_of_coordinate`: the identity-induced
pullback sends each coordinate to itself, as does the diagonal restriction.
For `strongHom_comp`, choose an admissible chart chain from `R` through `Q` to
`P`. `StrongHom.compOfDirected_pullback` computes the composite bounded map.
The two pullback formulas show its coordinate value is the image of
`g (f (P.map (MvPolynomial.X t)))`, also the value for `g.comp f`.
Coordinate extensionality proves the complete composition equality.

## Saturation

`saturationExtension_congr` transports equality of strong maps to equality of
their extensions; proof irrelevance removes the dependence on coherence
proofs. `compatibleHom P Q f` equips the induced strong map with the local
compatibility obtained from `strongHom_hasCoherentPullbacks`.
`saturatedHom_eq_compatible` records the definitional equality between its
extension and `saturatedHom`.

`saturatedHom_id` combines the strong identity with
`CompatibleStrongHom.saturationExtension_id`. For composition,
`compOfDirected_eq_comp` identifies the directed strong composite with the
underlying map of the compatible composite. It uses
`StrongHom.ext_of_coherent`: the base maps agree definitionally, while one
admissible chain per source chart gives equal complete pullbacks by
`StrongHom.compOfDirected_pullback` and `CompatibleStrongHom.comp_pullback`.
`saturatedHom_comp` transports the strong composition equality through this
comparison and applies `CompatibleStrongHom.saturationExtension_comp`.
This is exactly categorical composition of the saturated presentations.

## Localization and presentation independence

The main theorem applies those saturation lemmas to the original strong-map
identity and composition. Applying `localizationFunctor` gives the localized
identity and composition through `Functor.map_id` and `Functor.map_comp`.

For the final clause, the same universe-polymorphic helpers are applied with
all three algebras equal to `A` and both algebra maps the identity. The equality
`AlgHom.id_comp`, the saturation composition law and the localization functor
show that both composites of the morphisms induced between `P` and `P'` are
identities. Thus the inverse of `localizedHom K P P' (AlgHom.id K A)` is
`localizedHom K P' P (AlgHom.id K A)`; these two equations construct `IsIso`.

The proof concerns the five affine categorical clauses only. Its strong-map
steps prove equality of the full bounded maps, not merely equality of their
actions on points. It uses no seminorm comparison and adds no assumptions to
the published statement.

Development compilation of this module succeeded with zero errors or warnings.
Declaration inspection reports the independent universe parameters `u`, `v`,
`w`, `x` and only `propext`, `Classical.choice`, and `Quot.sound`.
