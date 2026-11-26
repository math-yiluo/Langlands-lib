# Relative identity components of smooth integral models

This helper module is used to build the integral-model family of
Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (KP). For a bounded
subset `Ω`, KP Theorem 8.3.2 (printed p. 296, PDF p. 327) gives a smooth model
`G^1_Ω`. KP Theorem 8.3.13 (printed p. 299, PDF p. 330) takes its relative
identity component `G^0_Ω` as the neutral model. The Library structure
`RelativeComponentModelData R K G` packages such a pair: a smooth full model,
a smooth neutral model with connected fibres, and an inclusion that represents
the relative identity component (SGA 3, Exposé VI_B, Definition 3.1).

This module proves one fact about that structure: every smooth model over a
discrete valuation ring, of a group with connected underlying space, is the
full model of such a datum. KP uses this without a numbered statement. It is
derived here from the definition and from Library results on relative identity
components.

The companion fact, that the neutral model is determined by the full model also
after a change of coefficients, is the Library lemma
`RelativeComponentModelData.baseChange_neutral_integralPoints_eq` (module
`Langlands.BruhatTits.IntegralModels.RelativeComponentFunctoriality`).

## Identity components over a field

- `IdentityComponent.map_identityPoint`: a homomorphism `f : A → B` of group
  schemes over a field sends the identity point of `A` to the identity point of
  `B`. This holds because `f` is compatible with the unit sections (`IsMonHom`).
- `IdentityComponent.mapsTo_identitySet`: such an `f` maps the identity
  component of `A` into the identity component of `B`. The image of a
  connected set is connected, and it contains the identity point of `B`.

## The relative identity-component criterion

Let `S` be a scheme and `G` a group scheme over `S`.

- `InRelativeIdentityComponent.comp`: if a `T`-point `x` of `G` lies in the
  relative identity component (on every fibre over a point `s` of `S`, its
  image lies in the identity component of `G_s`), then so does `x ≫ f` for any
  homomorphism `f : G → G'`. On each fibre, use `mapsTo_identitySet` for the
  base change of `f` to the residue field.
- `IsRelativeIdentityComponent.comp_iso`: let `i : H → G` represent the
  relative identity component of `G` and let `e : G ≅ G'` be an isomorphism.
  Then `i ≫ e.hom` represents the relative identity component of `G'`. It is
  an open immersion, being an open immersion followed by an isomorphism. A
  `T`-point `x` of `G'` factors through `i ≫ e.hom` exactly when `x ≫ e.inv`
  factors through `i`. By the previous lemma, applied to `e.hom` and `e.inv`,
  this is the case exactly when `x` lies in the relative identity component.
- `isRelativeIdentityComponent_id_of_connectedSpace`: over a field, if the
  underlying space of `G` is connected, then `𝟙 G` represents the relative
  identity component of `G`. The base is a single point, so the fibre is
  homeomorphic to all of `G` (Library `Scheme.Hom.fiberHomeo`). The fibre is
  therefore connected, and its identity component is everything.

## Relative-component data

Let `R` be a domain with fraction field `K`, and `G` a group scheme over `K`.

- `RelativeComponentModelData.exists_full_eq`: let `R` be a discrete valuation
  ring, let the underlying space of `G` be connected, and let `M` be a smooth
  integral model of `G`. Then there is a datum `D` with `D.full = M`.
  The steps:
  - The Library result `RelativeIdentityComponent.smoothExistence` gives a
    smooth group scheme `H` with geometrically connected fibres and a morphism
    `i : H → M.group` that represents the relative identity component.
  - `RelativeIdentityComponent.smoothDvrAffineness` (Prasad–Yu, *On
    quasi-reductive group schemes*, §3.5) makes `H` affine over `R`. It
    applies because the integral model `M` is affine over `R`.
  - Relative identity components commute with base change
    (`IsRelativeIdentityComponent.baseChange`). Composing with `M.genericIso`
    (`comp_iso`) gives a representative of the relative identity component of
    `G`, and so does `𝟙 G` (previous lemma).
  - Uniqueness (`IsRelativeIdentityComponent.iso`, `iso_hom_comp`) then gives
    a generic identification of `H` with `G` for which `i` commutes with the
    generic identifications. This makes `H` an integral model `N` and `i` a
    model homomorphism `N → M` over `𝟙 G`.

## Sources

- KP Theorem 8.3.2 (printed p. 296, PDF p. 327): `G(K)^1_Ω` and `G(K)^†_Ω`
  are schematic, with the same relative identity component.
- KP Theorem 8.3.13 (printed p. 299, PDF p. 330): the relative identity
  component `G^0_Ω` of `G^1_Ω` satisfies `G^0_Ω(O) = G(K)^0_Ω`.
- SGA 3, Exposé VI_B, Definition 3.1 (relative identity component), as cited
  by the Library module `Langlands/GroupScheme/RelativeIdentityComponent.md`.
- G. Prasad and J.-K. Yu, *On quasi-reductive group schemes*, §3.5 (the
  neutral component of a smooth affine group over a DVR is affine), as cited by
  `Langlands/GroupScheme/RelativeIdentityComponentDvrAffinenessStatement.md`.
