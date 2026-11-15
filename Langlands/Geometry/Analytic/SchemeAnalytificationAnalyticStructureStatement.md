# Statement: the glued analytification of a scheme is an analytic space

`SchemeAnalytificationAnalyticStructureStatement` states that the published
glued space `SchemeAnalytification.Space K f` of a scheme `X` locally of finite
type over `K` carries an analytic-space structure built from the affine
analytifications of the affine opens. Concretely, `Space K f` is homeomorphic to
the space of a saturated presentation `S`, and the affine analytification of
every affine open `U` is isomorphic, in the Library's localized category, to an
analytic domain of `S` over the canonical map `ι K f U`. These isomorphisms are
compatible with the morphisms of affine analytifications induced by inclusions
of affine opens. It is a `Prop`-valued definition; this unit supplies no proof.

## Provenance

Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*
(1990), Theorem 3.4.1, printed p.63/PDF p.77, constructs the analytification
`X^an` of a scheme `X` locally of finite type over `k` for nontrivially valued
`k`. Step (2) of its proof, printed p.64/PDF p.78, shows that the
analytification of an open subscheme of `Y` is the open subset `π⁻¹(X)` of
`Y^an` with the induced structure. Step (3), on the same page, covers `X` by
affine open subschemes and glues their analytifications. The registered source
is `provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
Definition 1.3.1, printed p.23/PDF p.20, defines analytic domains: subsets in
which the contained affinoid domains restrict to a net, with the canonical
morphism `ν : Y → X`. Proposition 1.3.3, printed p.24/PDF p.21, with its proof
on printed p.25/PDF p.22, glues analytic spaces `X_i` along open analytic
domains `X_ij`. The glued space `X` has morphisms `μ_i : X_i → X` such that
(1) `μ_i` is an isomorphism of `X_i` with an analytic domain of `X`, (2) the
`μ_i(X_i)` cover `X`, (3) `μ_i(X_ij) = μ_i(X_i) ∩ μ_j(X_j)`, and (4)
`μ_i = μ_j ∘ ν_ij` on `X_ij`. The analytic spaces of the 1993 paper are the
Library's localized category of saturated presentations
(Definitions 1.2.7–1.2.9 and the category of fractions, printed pp.18–20/PDF
pp.15–17). The registered source is `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed
p.19, final paragraph of the proof of Proposition 5.11(3), appeals to the
functorial analytification `X^an` of Conrad–Temkin, in the rigid-analytic sense,
for separated algebraic spaces locally of finite type over a complete
non-archimedean field, compatible with open immersions and with the scheme
case. Only the Berkovich-style analytic structure on the analytification of a
scheme is stated here. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The formulation is derived. It applies the gluing description of Proposition
1.3.3 to the published glued space, whose points and topology are built from
the affine polynomial loci without any analytic structure. The analytic
structure is asserted to exist, not constructed. Assertions 1 and 2 are
properties (1) and (2) of Proposition 1.3.3 read through the homeomorphism `e`.
Assertion 3 is the compatibility (4) for an inclusion `V ≤ U` of affine opens.
For affine opens, step (2) of Berkovich's proof identifies `V^an` with an open
subset of `U^an`.

## Hypotheses

The field `K : Type u` is nontrivially normed, ultrametric and complete.
`X : Scheme.{u}` is a scheme with a morphism `f : X ⟶ Spec K` that is locally of
finite type. No separatedness, quasi-compactness, reducedness or nonemptiness is
assumed.

For an affine open `U`, `chartPresentation K f U` is the published chosen finite
polynomial presentation of the global sections of `U`, and
`AffineAnalytification.localized K (chartPresentation K f U)` is the published
affine analytification of `U` in the localized category. `ι K f U` is the
canonical continuous map from its space `LocalSpace K f U` into `Space K f`. For
affine opens `V ≤ U`, `restriction f h` is the restriction of global sections,
and `AffineAnalytification.localizedHom` is the published morphism
`V^an ⟶ U^an` it induces.

For a saturated presentation `S`, `S.AnalyticDomain` is the Library's type of
analytic domains, matching Definition 1.3.1. `S.domain D` is the domain `D` with
the charts of `S` contained in it, and `S.localizedDomainInclusion D` is the
image in the localized category of the canonical morphism `ν : D → S`.
`localizationFunctor` and `localizedSpaceFunctor` are the Library's
localization functor and the underlying-space functor of the localized
category.

## The statement

For all such `K`, `X` and `f`, there exist

* a saturated presentation `S : SaturatedAtlasPresentation.{u, u, u} K`;
* a homeomorphism `e : S.presentation.space ≃ₜ Space K f`;
* for every affine open `U`, an analytic domain `D U : S.AnalyticDomain`;
* for every affine open `U`, an isomorphism in the localized category
  `φ U : AffineAnalytification.localized K (chartPresentation K f U) ≅
  localizationFunctor.obj (S.domain (D U))`;

such that the following hold.

1. For every affine open `U`, `e '' (D U).carrier = Set.range (ι K f U)`.
2. For every affine open `U` and every `y : LocalSpace K f U`, applying `e` to
   the image of `y` under the underlying continuous map of
   `(φ U).hom ≫ S.localizedDomainInclusion (D U)` gives `ι K f U y`.
3. For affine opens `U`, `V` with `h : V ≤ U`,
   `localizedHom K (chartPresentation K f U) (chartPresentation K f V)
   (restriction f h) ≫ (φ U).hom ≫ S.localizedDomainInclusion (D U)` equals
   `(φ V).hom ≫ S.localizedDomainInclusion (D V)`.

Assertion 1 also follows from assertion 2, because `φ U` is an isomorphism and
the inclusion of `D U` has range `D U`; it is stated separately for clarity.
Since every point of `Space K f` lies in the image of some `ι K f U`, the
domains `D U` cover the space of `S`.

## Truth sketch

This is not a Lean proof. Take for `S` the saturation of the atlas on
`Space K f` whose charts are the images of the affinoid domains of the affine
analytifications. Bounded restriction maps between nested charts coming from
different affine opens `U` and `U'` exist because the image of a chart of `U`
inside `U'^an` is an affinoid domain there. When `U ∩ U'` is not affine, this
requires covering the chart by finitely many affinoid pieces lying over affine
opens of `U ∩ U'`, and gluing bounded maps by Tate's acyclicity theorem. Take
`D U` to be the preimage of the open set `Set.range (ι K f U)`. Open subsets are
analytic domains here because affinoid neighbourhoods form a basis at each
point. Take `φ U` to be the image under `localizationFunctor` of the strong map
from the saturated affine analytification of `U` to `S.domain (D U)` whose
underlying map is `e⁻¹ ∘ ι K f U`. This strong map is a quasi-isomorphism. Assertion 3 then holds because both sides are images of
strong maps with the same underlying map whose bounded pullbacks are induced by
the same restriction maps of affinoid algebras. The topological input is the
published but unproved `SchemeAnalytificationGluingStatement`.

## Scope

The statement does not construct the analytic structure, does not prove its
uniqueness, and does not assert the universal property of Theorem 3.4.1 or the
functoriality of the structure in `X`. It does not cover the center map,
rational points, extension of the ground field, closed immersions, separated
or Hausdorff conditions, or fibre products.
