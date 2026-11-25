# Polynomial-locus analytification of genuine affine schemes

This construction uses Mathlib's actual affine schemes. For a scheme morphism
`f : X → Spec K`, `CoordinateRing f` is precisely the global-section ring
`Γ(X, ⊤)`, with its `K`-algebra structure induced by the global-section map of
`f` and the canonical inverse `K → Γ(Spec K, ⊤)`. The named carrier retains
`f` to disambiguate this scalar action; it introduces no quotient or assumed
coordinate algebra. The rings and schemes use a common universe, as required
by Mathlib's native scheme morphisms.

If `X` is affine and `f` is locally of finite type, `coordinateRingFiniteType`
proves that this algebra is finite type. Since an affine scheme is compact,
this covers affine finite-type schemes. The proof applies Mathlib's affine
finite-type criterion to `f.appTop` and composes with the canonical ring
isomorphism for `Spec K`. `coordinateIso f` is Mathlib's canonical actual
scheme isomorphism `X ≅ Spec Γ(X, ⊤)`. `coordinateIso_hom_over` proves that its
forward map respects the given map to `Spec K`, using naturality of the
canonical map to the spectrum of global sections. `presentation f` chooses
a finite polynomial surjection to this actual algebra.

`Presentation f A` stores only algebraic presentation data: a finite polynomial
surjection to `A`, an actual scheme isomorphism from `X` to `Spec A`, and its
compatibility with the base map. It stores no analytic existence or comparison
assumption. `Presentation.forSpec P` uses the genuine `Spec A` scheme and its
identity isomorphism, retaining exactly the supplied polynomial presentation
`P`. `forSpecFiniteType` chooses `P` from finite generation. `forAffine f P`
uses the actual global-section algebra and the canonical affine isomorphism;
`forAffineFiniteType f` also chooses its polynomial surjection automatically.
The scheme isomorphism and all chosen algebraic data remain visible.

For a nonarchimedean normed field and a scheme presentation `C`,
`boundedAlgebra C r`, `boundedPolynomialMap C r` and `boundedAlgebraMap C r`
expose the actual polynomial-locus quotient and its structural maps at any
positive polyradius `r`. `boundedPolynomialMap_relation` kills every polynomial
in the given kernel, and `boundedAlgebraMap_map` and `boundedAlgebraMap_comp`
prove the polynomial factorization. `boundedRestriction C r s hsr` is the full
bounded quotient restriction for coordinatewise `s ≤ r`, with structural compatibility proved
by `boundedRestriction_polynomialMap` and `boundedRestriction_algebraMap`.
`boundedRestriction_self` and `boundedRestriction_trans` are equalities of
the full bounded algebra maps. These reuse the actual closed-kernel
quotients and algebra maps from `PolynomialLocusCharts`; the maps are not
specified only on spectrum points. No nontriviality or reducedness assumption
on the coordinate algebra is imposed, and zero polynomial arity is permitted.

For a complete nontrivially normed nonarchimedean field,
`chartAlgebra C m` specializes to the cofinal radius
`‖AnalyticAffineSpace.scale K‖⁻¹ ^ m`.
`chartPolynomialMap C m` and `chartAlgebraMap C m` retain the actual polynomial
and coordinate-algebra maps. `chartRestriction C h` is the bounded restriction
for `m ≤ k`, and `chartRestriction_algebraMap` proves its compatibility with
the coordinate-algebra map. `chartSystem C` contains the proved affinoid-domain
restrictions. `Space C`, `chart C m` and `exists_chart` expose the actual
topological glue and its covering by these spectra. This is computed from
`C.polynomialPresentation` using `AffineAnalytificationGluing`.

`atlas C` and `analyticPresentation C` compute the actual affinoid atlas and
`AffinoidAtlasPresentation.{u,u,0} K`. They use
`AffineAnalytificationAtlas`'s least original natural index for each distinct
chart range. Each selected chart keeps its original full quotient algebra and
bounded restriction maps; omitted original charts have explicit bounded
equivalences to their selected representatives, constructed from the full
affinoid-domain universal properties over a common larger chart. Equal point
sets alone are not used to identify algebras. This construction permits
repeated and empty ranges without a positive-arity or nonzero-algebra premise.

`saturated C : SaturatedAtlasPresentation.{u,u,u} K` computes the existing
full-domain saturation of this atlas. `localized C` applies the existing
localization functor, giving an object of
`SaturatedAtlasPresentation.LocalizedCategory.{u,u,u} (K := K)`.
`analyticPresentation_space`, `saturated_space` and `localized_space`
are definitional equalities recording that the literal topological space
is the constructed `Space C`. None of these outputs is a field of
`Presentation`, and none requires an assumed analytification or comparison.

The named construction `spec P` gives the localized analytification of the
genuine scheme `Spec A` with precisely the supplied polynomial presentation.
`specFiniteType` chooses that presentation from `Algebra.FiniteType K A`.
`affine f P` gives the localized object for an actual affine scheme
`f : X → Spec K` using the specified polynomial presentation of its actual
global sections. `affineFiniteType f` derives finite generation from
`IsAffine X` and `LocallyOfFiniteType f` and chooses the presentation.
The complete underlying algebraic data and unlocalized atlas are available
through `Presentation.forSpec`, `forSpecFiniteType`, `forAffine` and
`forAffineFiniteType` and the methods just described.

This is derived scheme-input packaging for the construction in Berkovich,
*Spectral Theory and Analytic Geometry over Non-Archimedean Fields* (1990),
proof of Theorem 3.4.1, steps (1)--(3), printed p.64/PDF p.78, registered as
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.
The explicit global-section type and Mathlib isomorphism interface are internal
choices implementing the passage from finite-type affine schemes to their
coordinate algebras.

The bounded chart and atlas implementation is reused by Lean name from
`PolynomialLocusCharts`, `AffineAnalytificationGluing` and
`AffineAnalytificationAtlas`. The full polynomial kernels and algebra maps
remain visible throughout; no radical or reduced replacement is made.
The zero algebra, nonreduced algebras, empty affine schemes and zero-variable
presentations are permitted.

General independence of presentation, functoriality for all affine scheme
morphisms, rational-point and point-topology comparisons, the analytification
universal property, and arbitrary analytic field-extension comparisons lie
outside this module. The constructed localized object
and its intrinsic chart laws alone do not prove the final analytification
bridge.
