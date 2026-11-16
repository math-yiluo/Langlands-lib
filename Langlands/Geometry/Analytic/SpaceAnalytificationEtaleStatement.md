# Analytifications of algebraic spaces detect étale morphisms

`SpaceAnalytificationEtaleStatement` says the following. Let `K` be a complete
ultrametric nontrivially normed field, and let `f : X' ⟶ X` be a morphism of
algebraic spaces over `Spec K`, both separated and locally of finite type. Let
`(Y', p')` be an analytification of `X'` and `(Y, p)` one of `X`, in the sense
of `IsAnalytification`. Let `F : Y' ⟶ Y` be a morphism in the Library's
localized category with `p' A P x ≫ F = p A P (RingPoints.map f x)` for every
affine test point `x` of `X'`. Then `f` is étale if and only if `F` is étale.
This module states the proposition only; it supplies no proof.

## Statement

The statement quantifies over a universe `u` and:
- a field `K : Type u` with `NontriviallyNormedField K`, `IsUltrametricDist K`
  and `CompleteSpace K`;
- algebraic spaces `X'` and `X` over `Spec (CommRingCat.of K)` and a morphism
  `f : X' ⟶ X`;
- hypotheses `IsSeparated X'`, `LocallyOfFiniteTypeOverBase X'`,
  `IsSeparated X` and `LocallyOfFiniteTypeOverBase X`;
- objects `Y'` and `Y` of `LocalizedCategory.{u, u, u}`, families
  `p' : PointFamily K X' Y'` and `p : PointFamily K X Y`, and hypotheses
  `IsAnalytification K X' Y' p'` and `IsAnalytification K X Y p`;
- a morphism `F : Y' ⟶ Y` and the compatibility hypothesis
  `∀ A P x, p' A P x ≫ F = p A P (RingPoints.map f x)`, over commutative
  `K`-algebras `A` in universe `u`, finite polynomial presentations `P` of `A`
  and points `x : RingPoints K X' A`.

The conclusion is `IsEtaleMorphism f ↔ SaturatedAtlasPresentation.etale F`.

- `IsEtaleMorphism f` is the Library's étaleness of morphisms of algebraic
  spaces (module `HenselianSpacePointTopologyStatement`, Stacks Project Tag
  03FR): for every scheme `U` over `Spec K` and every étale morphism
  `φ : U → X'`, the composite `φ ≫ f` is étale.
- `SaturatedAtlasPresentation.etale F` is the Library's étaleness in the
  localized category (module `EtaleSite`): `F` is isomorphic, as an arrow, to
  the image of a strong map between constructed saturations that is étale over
  all affinoid pieces at every point.

By `SpaceAnalytificationMorphismStatement`, `F` is the unique morphism
compatible with `f`, that is, the analytification of `f`. This statement does
not depend on that one; it takes `F` as a hypothesis.

## Provenance

The source is Conrad–Temkin, *Non-archimedean analytification of algebraic
spaces* (2009), registered as
`conrad-temkin-2009-nonarchimedean-analytification`, SHA256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`.
- Theorem 2.3.1, printed p.11 (rigid-analytic setting): for a map `f : X → Y`
  of analytifiable algebraic spaces, `f` is étale if and only if `fᵃⁿ` is.
  The proof works étale-locally on `Y` and reduces to the scheme case.
- Printed p.19, last paragraph of §4.1: the arguments of §2 carry over to
  `k`-analytic quotients, which are independent of the chart and functorial in
  `X`.
- Printed p.20, after Theorem 4.2.1: the analytified chart `ℛ ⇉ 𝒰` of a
  separated algebraic space is an étale equivalence relation by Berkovich's
  dictionary [Ber2, 3.3.11].

The scheme case is Berkovich, *Étale cohomology for non-Archimedean analytic
spaces* (1993), registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
Proposition 3.3.11, printed p.64/PDF p.61: a morphism of schemes locally of
finite type over `Spec(𝒜)`, for a `k`-affinoid algebra `𝒜`, is unramified
(resp. étale) if and only if its analytification is. Its affine case over `K`
is the Library's `AffineAnalytificationEtaleStatement`.

The second source is Conrad, *Weil and Grothendieck approaches to adelic points*
(2011), registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. Printed
p.19, proof of Proposition 5.11(3), describes the analytification of [CT] as
compatible with "étale maps", among other properties.

The formulation is derived. Conrad and Conrad–Temkin's Theorem 2.3.1 concern
rigid-analytic spaces. Conrad–Temkin note on p.19 that étaleness is a weaker
condition in rigid geometry than in `k`-analytic geometry. This statement uses
Berkovich's `k`-analytic étaleness, as modelled by the Library's `etale`, and
its analytic spaces are objects of the Library's localized category. The
analytification of `f` is expressed by the compatibility hypothesis on `F`.
Only nontrivially normed `K` is treated, as the Library's affine
analytifications require.

## Why the statement should be true

This is not a Lean proof. Choose étale points `x'ᵢ : Spec A'ᵢ → X'` whose images
cover `X'`. By `IsAnalytification`, the maps `p'(x'ᵢ)` are étale and jointly
surjective onto `Y'`.

- If `f` is étale, each `f ∘ x'ᵢ` is an étale point of `X`, so
  `p'(x'ᵢ) ≫ F = p(f ∘ x'ᵢ)` is étale. Étaleness of `F` then follows because
  it is local on the source for étale coverings. Flatness and unramifiedness
  at a point descend along the étale maps `p'(x'ᵢ)`. Boundarylessness descends
  by the composition rule `Int(Z/X) = Int(Z/Y) ∩ ψ⁻¹(Int(Y/X))` for relative
  interiors. This rule is Berkovich, *Spectral Theory and Analytic Geometry
  over Non-Archimedean Fields* (1990), Proposition 3.1.3(ii), printed
  p.49/PDF p.63, registered as
  `provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
  SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.
- If `F` is étale, let `φ : U → X'` be étale with `U` a scheme. Choose étale
  points `xⱼ : Spec Aⱼ → X` covering `X`, and cover each scheme
  `U ×_X Spec Aⱼ` by affine opens `Spec Bₖ`. The composite
  `Spec(Bₖ)ᵃⁿ → Y' → Y` is étale, as `Spec Bₖ → X'` is étale and `F` is étale.
  It equals `Spec(Bₖ)ᵃⁿ → Spec(Aⱼ)ᵃⁿ → Y`, and `p(xⱼ)` is étale. The first map
  is quasifinite: its fibres lie in those of the étale composite, and it is
  boundaryless by the interior rule above. For good spaces this gives
  finiteness at every point (Berkovich 1993, Proposition 3.1.4, printed
  p.55/PDF p.52).
  Berkovich 1993, Corollary 3.3.9, printed p.63/PDF p.60, then shows that
  `Spec(Bₖ)ᵃⁿ → Spec(Aⱼ)ᵃⁿ` is étale. By Proposition 3.3.11,
  `Spec Bₖ → Spec Aⱼ` is étale. These maps cover the base change of `φ ≫ f`
  along the covering `Spec Aⱼ → X`, so `φ ≫ f` is étale.

The proof must also realize these Berkovich facts in the Library's localized
category and identify the Library's `etale` with Berkovich's notion.
