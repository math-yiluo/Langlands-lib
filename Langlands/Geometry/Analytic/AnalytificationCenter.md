# Berkovich's center map from an analytification to its scheme

This module defines the underlying continuous map of Berkovich's canonical morphism
`π : X^an → X`, for the Library's polynomial-locus analytification. It does this
first for an affine analytification `Space K P` of a presented `K`-algebra `A`,
with values in the prime spectrum of `A`. It then does it for the glued
analytification `Space K f` of a scheme `X` locally of finite type over `K`, with
values in `X`. A point goes to the prime ideal on which its multiplicative
seminorm vanishes. The module proves that these maps are continuous, natural for
the maps induced by `K`-algebra maps, and compatible with the gluing. It does not
prove that `π` is surjective or describe its fibres. Surjectivity and the fibres
over `K`-rational points are stated in `AnalytificationCenterStatement` and
proved in `AnalytificationCenterProof`.

## Provenance

Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*
(1990), §3.4, printed pp.63–64/PDF pp.77–78. Theorem 3.4.1 says that for a
scheme `X` locally of finite type over `k` the functor `𝒳 ↦ Hom_k(𝒳, X)` is
represented by a `k`-analytic space `X^an` together with a morphism
`π : X^an → X`. Part (i) adds that `π` is surjective and induces a bijection
on closed points. Section 3.4 assumes a nontrivial valuation, as
`NontriviallyNormedField` does here. Step (3) of the proof builds `X^an` for
general `X` by gluing the analytifications of affine opens. Remark 3.4.2 says
that for `X = Spec(A)`, with `A` finitely generated over `k`, the space `X^an`
is the set of multiplicative seminorms on `A` whose restriction to `k` is the
norm of `k`. The registered source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

Conrad–Temkin, *Non-archimedean analytification of algebraic spaces* (2009),
§4.1, printed p.20/PDF p.20, uses "the fact that the natural map `W^an → W` is
surjective" for an algebraic `k`-scheme `W`. The registered source is
`conrad-temkin-2009-nonarchimedean-analytification`, SHA256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`.

Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed
p.19, final paragraph of the proof of Proposition 5.11(3), works with the
analytification `X^an` of [CT]. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The sources do not write down the point map of `π` as a formula. The kernel
description below is derived. A morphism of locally ringed spaces to `Spec(A)`
sends a point `x` to the kernel of `A → κ(x)`. For a point `x` of `X^an` given
by a seminorm `|·|_x`, the residue field `κ(x)` embeds into the completed
residue field `H(x)`, whose absolute value restricts to `|·|_x` on `A`. So that
kernel is `{a ∈ A : |a|_x = 0}`. The gluing over affine opens follows step (3)
of Berkovich's proof. The passage through `Spec Γ(U, ⊤)` and the canonical
isomorphism `U ≅ Spec Γ(U, ⊤)` is an implementation choice with no source
counterpart.

## Hypotheses

The first part lies in `Langlands.Analytic.AffineAnalytification`. `K` is a
nontrivially normed, ultrametric and complete field. `A` is a commutative
`K`-algebra with a finite polynomial presentation
`P : FinitePolynomialPresentation K A`. For naturality, `B` is another such
algebra with presentation `Q`, and `f : A →ₐ[K] B` is a `K`-algebra map.

The second part lies in `Langlands.Analytic.SchemeAnalytification`. `K` is as
above. `f : X ⟶ Spec (CommRingCat.of K)` is `LocallyOfFiniteType`, with `X` in
the universe of `K`. No separatedness, quasi-compactness or nonemptiness of `X`
is assumed.

## The affine center map

- `kernel K P x : Ideal A` is the set of `a : A` with
  `pointSeminorm K P x a = 0`, where `pointSeminorm` is the published
  multiplicative seminorm of a point. It is an ideal because the seminorm is
  subadditive, nonnegative and multiplicative. `mem_kernel` is the membership
  criterion.
- `kernel_isPrime`: the kernel is a prime ideal. It does not contain `1`,
  because a multiplicative ring seminorm takes the value `1` at `1`. If it
  contains a product `a * b`, it contains `a` or `b`, because the seminorm is
  multiplicative and the real numbers have no zero divisors.
- `center K P x : PrimeSpectrum A` is this prime ideal, and `center_asIdeal`
  records its underlying ideal. `center_mem_basicOpen`: `center K P x` lies in
  the basic open set of `a` exactly when `pointSeminorm K P x a ≠ 0`.
- `continuous_center`: `center K P` is continuous for the Zariski topology. The
  preimage of the basic open set of `a` is the set where the published
  continuous function `x ↦ pointSeminorm K P x a` is nonzero, and basic open
  sets form a basis. `centerMap K P : C(Space K P, PrimeSpectrum A)` bundles the
  map, with `centerMap_apply`.
- `pointSeminorm_baseMap`: for the published continuous map
  `baseMap K P Q f : Space K Q → Space K P` induced by `f`,
  `pointSeminorm K P (baseMap K P Q f y) a = pointSeminorm K Q y (f a)`. The proof
  reduces to a chart point and uses the published `chartMap_algebraMap`.
- `kernel_baseMap`: `kernel K P (baseMap K P Q f y)` is the preimage under `f`
  of `kernel K Q y`. `center_baseMap`: `center K P (baseMap K P Q f y)` is
  `PrimeSpectrum.comap f (center K Q y)`. Thus the center map is natural.

## The center map of a scheme

- `affineOpenMap U : Spec Γ(U, ⊤) ⟶ X`, for `U : X.affineOpens`, is the
  inverse of Mathlib's canonical isomorphism `U ≅ Spec Γ(U, ⊤)` followed by
  the inclusion `U.ι` of the open subscheme.
- `localCenterPoint K f U y` is the affine center of a point `y` of the
  published analytification `LocalSpace K f U` of `U`. It is computed for the
  chosen presentation `chartPresentation K f U` of the global sections and
  read as a point of `Spec Γ(U, ⊤)`. `continuous_localCenterPoint` records its
  continuity.
- `localCenterPoint_localMap`: for affine opens `V ≤ U`, the center of the image
  of `y` under the published map `localMap K f h` is the image of the center of
  `y` under `Spec` of the restriction `Γ(U, ⊤) → Γ(V, ⊤)`. This is
  `center_baseMap` for the published restriction algebra map.
- `localCenter K f U : C(LocalSpace K f U, X)` is `affineOpenMap U` composed
  with `localCenterPoint K f U`. `localCenter_apply` unfolds it.
- `localCenter_localMap`: `localCenter K f U (localMap K f h y) = localCenter K
  f V y` for `V ≤ U`. The proof uses `localCenterPoint_localMap`, Mathlib's
  naturality of the inverse of `isoSpec` and the identity
  `X.homOfLE h ≫ U.ι = V.ι`.
- `center K f : C(Space K f, X)` is Berkovich's map `π` on the published glued
  space. It is the published descent `desc` of the family `localCenter K f`
  through the compatibility `localCenter_localMap`. `center_ι` records that
  `center K f (ι K f U y) = localCenter K f U y`.
- `center_ι_mem`: the center of a point coming from the analytification of an
  affine open `U` lies in `U`.

## Scope

The module imports the published `AffineAnalytificationSeminorm` and
`SchemeAnalytificationSpace`. It defines
only the underlying continuous map of `π`; no map of structure sheaves is
constructed. It does not state that the center map is surjective, that it
induces a bijection on closed points or on `K`-points, or that the preimage of
`U` under `center K f` is the image of `ι K f U`. It does not compare the center
map with the rational-point map of `SchemeAnalytificationRationalPoints`. Of
these claims, surjectivity, the preimage of `U` and the comparison with the
rational-point map are stated in `AnalytificationCenterStatement` and proved in
`AnalytificationCenterProof`.
