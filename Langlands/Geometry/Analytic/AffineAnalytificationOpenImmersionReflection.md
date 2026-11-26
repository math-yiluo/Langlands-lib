# Analytic open immersions of affine analytifications are algebraic

Let `K` be a complete, ultrametric, nontrivially normed field and let
`f : A →ₐ[K] B` be a map of commutative `K`-algebras with finite polynomial
presentations `P` and `Q`, with `A` and `B` in a common universe independent of
that of `K`.

## Declarations

- `SaturatedAtlasPresentation.openImmersion.mono`: an analytic open immersion
  is a monomorphism, being an isomorphism followed by the monic inclusion
  `domainι` of an open domain.
- `SaturatedAtlasPresentation.openImmersion.etale`: an analytic open
  immersion is étale. The inclusion of an open domain is étale by the
  published `etaleOpenDomainStatement`, an isomorphism is étale, and étale
  morphisms compose (`etale_comp`).
- `AffineAnalytification.isOpenImmersion_of_openImmersion_localizedHom`: if
  `localizedHom K P Q f` is an analytic open immersion, then
  `Spec.map (CommRingCat.ofHom f.toRingHom)` is an open immersion of schemes.

## Proof of the main theorem

The analytic open immersion is monic, so `f` is a ring epimorphism by
`epi_of_mono_localizedHom` and its spectrum map is a monomorphism of schemes
by `mono_specMap_of_epi`. The analytic open immersion is étale. The published
étale reflection (`isEtale_of_localizedHom_etale` followed by the étale clause
of `affineAnalytificationEtale`) makes `f` an étale ring map. Mathlib's
`HasRingHomProperty.Spec_iff` turns this into étaleness of the spectrum map,
which is therefore flat and locally of finite presentation. Mathlib's
`AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono` then shows that the
spectrum map is an open immersion.

## Provenance

This is the affine converse in Berkovich, *Spectral theory and analytic
geometry over non-Archimedean fields* (1990), Proposition 3.4.6(8), printed
p.65/PDF p.79, with its proof on printed p.66/PDF p.80, registered as
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.
Berkovich shows that the morphism is étale and radical. The Lean proof
replaces radicality by monicity, which it obtains from the self fibre product,
and uses Mathlib's flat-monomorphism criterion instead of the étale-radical
criterion.
