# Geometry of finite powers over a field

This internal module shows that finite powers of an affine, finite-type,
geometrically integral scheme over a field `k` are again of that kind. It is
used to control the ordered finite products in pointed-image generation. It
formalizes no literature assertion; it is assembled from Mathlib's
geometric-property and finite-product APIs.

General lemmas, over an arbitrary base and universe:

- The imported `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.subsingleton_spec_field`: `Spec k` has a single point. It is a local
  instance in this file. Mathlib uses it to see that every morphism to `Spec k` is
  flat and that irreducibility descends from geometric irreducibility.
- `geometricallyReduced_comp f g`: if `f` and `g` are geometrically reduced, `f`
  is flat and `g` is locally of finite type, then `f ≫ g` is geometrically
  reduced. For a field point `x` of the target, Mathlib's
  `pullbackRightPullbackFstIso` identifies the fibre of `f ≫ g` with the
  pullback of `f` along the fibre of `g`. That fibre of `g` is reduced by
  geometric reducedness of `g`. Mathlib's instances for pullbacks of
  geometrically reduced morphisms then make the pullback of `f` reduced, using
  flatness of `f` and finite type of `g`.
- `geometricallyReduced_of_isIso`, `geometricallyIrreducible_of_isIso`:
  isomorphisms are geometrically reduced and geometrically irreducible, since
  their base changes are isomorphisms onto the field spectrum.

`FinitePowerGood B` is the object property of `Over B` requiring the structure
morphism to be affine (`IsAffineHom`), locally of finite type, geometrically
reduced and geometrically irreducible.

Over `Spec k`:

- `finitePowerGood_of_iso` transports the property along isomorphisms.
- `finitePowerGood_tensor` shows the property is closed under the cartesian
  product `X ⊗ Y`. The structure morphism of the product is
  `pullback.fst X.hom Y.hom ≫ X.hom`. The first projection is a base change of
  `Y.hom`, so it is affine, of finite type, flat, geometrically reduced and
  geometrically irreducible. Composites of such morphisms keep these properties,
  using `geometricallyReduced_comp` and Mathlib's
  `GeometricallyIrreducible.comp`.
- Two private instances show the property is closed under empty limits (the
  terminal object is `Spec k` itself) and binary products. Hence it is closed
  under finite products.
- `finitePowerGood_finitePower V hV n`: the published `finitePower V n`, the
  `n`-fold product of `V` in `Over (Spec k)`, inherits the property from `V`.
- `finitePowerGood_of_geometricallyIntegral`: an affine, locally finite-type,
  geometrically integral `V` has the property.

Consequences for an object `X` with the property:

- `FinitePowerGood.isAffine`: `X.left` is affine.
- `FinitePowerGood.isLocallyNoetherian`: `X.left` is locally Noetherian, being
  locally of finite type over a field.
- `FinitePowerGood.isIntegral`: `X.left` is integral. It is irreducible by
  geometric irreducibility over the one-point `Spec k`, and reduced by Mathlib's
  `GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian`.

No separability, perfectness or characteristic hypothesis on `k` is used.

The field-spectrum instance is reused from the attributed Anthropic FLT port;
its source and license are retained in that module and
`licenses/Anthropic-FLT/`. No new field-spectrum theorem is introduced.
