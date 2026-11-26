# Analytifications of étale algebra maps are étale

This module contains only the Prop-valued definition
`Langlands.Analytic.AffineAnalytification.AffineAnalytificationLocalizedEtaleStatement`:
the analytification `Spec(B)ᵃⁿ → Spec(A)ᵃⁿ` of an étale map of `K`-algebras of
finite type is étale in the Library's localized category. The file states the
proposition and does not prove it.

## Exact statement

`AffineAnalytificationLocalizedEtaleStatement.{u, v, w} : Prop` asserts: for
every field `K : Type u` with `NontriviallyNormedField K`, `IsUltrametricDist K`
and `CompleteSpace K`, all commutative `K`-algebras `A : Type v` and
`B : Type w` with finite polynomial presentations
`P : FinitePolynomialPresentation K A` and `Q : FinitePolynomialPresentation K B`
(surjections from polynomial rings in finitely many variables), and every
`K`-algebra map `f : A →ₐ[K] B`, if `f` is étale (`f.toRingHom.Etale`), then
`SaturatedAtlasPresentation.etale (localizedHom K P Q f)`.

- `localizedHom K P Q f : localized K Q ⟶ localized K P` is the Library's
  analytification of `Spec f`, the image in the localized category of the
  strong map `saturatedHom K P Q f` (module
  `Langlands.Geometry.Analytic.AffineAnalytificationLocalizedMap`).
- `SaturatedAtlasPresentation.etale` is the Library's localized étale predicate
  (module `Langlands.Geometry.Analytic.EtaleSite`).
- The universes of `K`, `A` and `B` are independent.

## Source

Berkovich, *Spectral theory and analytic geometry over non-Archimedean fields*
(1990), registered as
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`:
Proposition 3.4.6, printed p.65 (PDF p.79), in §3.4 "GAGA: the case of
nontrivial valuation" (begins printed p.63): for a morphism `φ : Y → X` of
schemes locally of finite type over `k`, `φ` is (3) étale if and only if `φᵃⁿ`
is étale. Its proof derives (3) from (1) (flatness) and (2) (unramifiedness).

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`:
Definition 3.3.4, printed p.63 (PDF p.60), a quasifinite morphism is étale if
it is unramified and flat; this is the notion the Library's `etale` formalizes.

## Why the statement is expected to hold

The statement is the "only if" direction of Proposition 3.4.6(3) for affine
source and target, `Y = Spec B` and `X = Spec A`. The Library's analytification
`localized K P` of `Spec A` is built from the presentation `P`, and the
predicate `etale` formalizes, through affinoid pieces, Berkovich's étale
morphisms (unramified and flat quasifinite; Berkovich 1993, Definition 3.3.4),
so the source proposition predicts the statement.

## Provenance: derived

The proposition is a derived specialisation of Berkovich 1990,
Proposition 3.4.6(3) (one direction, affine schemes) to the Library's objects
`AffineAnalytification.localized` and `localizedHom` and to the localized étale
predicate `SaturatedAtlasPresentation.etale`. Like that section of the source,
it assumes a nontrivial absolute value, which the Library's affine
analytifications require.

The Library statement `AffineAnalytificationEtaleStatement` (proved by
`affineAnalytificationEtale`) relates `f.toRingHom.Etale` to
`StrongHom.IsEtale` of `saturatedHom K P Q f` for the atlas presentations
`presentation K Q` and `presentation K P`, whose atlas index universe is `0`.
The localized predicate `etale` is defined through `StrongHom.IsEtaleAllPieces`
on presentations whose index universe equals the space universe. The module
`Langlands.Geometry.Analytic.AffineAnalytificationLocalizedEtaleReduction`
proves that the present statement at `.{u, u, u}` follows from
`AffineAnalytificationEtaleStatement.{u, u, u}` and a comparison of
`StrongHom.IsEtaleAllPieces` with `strongEtale` for presentations of atlas
index universe `0`.

## Place in the Library

At universes `.{u, u, u}` the proposition is word for word the fourth premise of
`Langlands.Analytic.SpaceAnalytification.ExistenceReduction.SpaceAnalytificationExistenceFiveInputReductionStatement`,
so `AffineAnalytificationLocalizedEtaleStatement.{u, u, u}` can be passed as
that premise of `spaceAnalytificationExistenceFiveInputReduction` without
conversion.
