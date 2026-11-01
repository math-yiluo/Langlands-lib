# Geometry of the finite integral-action equation locus

This internal derived module adds geometry to the actual equalizer in
`RelativeIntegralActionLocus`. It uses the same abelian scheme `B/S`, possibly
noncommutative ring `O` with finite integer basis, scheme `E/S`, and supplied
natural comparison of `E` with the canonical relative endomorphism presheaf on
all locally noetherian schemes over `S`. It assumes that `E → S` is separated
and locally of finite type; it does not construct `E` or prove these assumptions.

The finite-power lemmas apply to any scheme `E/S`, with a finite index type in
an arbitrary universe, including an empty type. They prove that finite relative
powers inherit local finite type and separatedness. When `S` is locally
noetherian, local finite type then proves local noetherianness of the power.
Local noetherianness of the factors alone is not used as a product-closure claim.

The proof uses a private categorical helper. For a morphism property stable
under base change and composition, the projection from a binary relative
product inherits the property from its other factor. Composing with the first
factor's structural map gives the property for the product. For a property
containing identities and respecting isomorphisms, this and the terminal
identity object prove closure under all finite products. The helper is
specialized to Mathlib's locally-of-finite-type and separated morphism
properties.

For any supplied proof of local noetherianness of the tuple power, the inclusion
of the existing action locus is a closed immersion: it is the equalizer of two
maps into the finite equation power, whose structural map is separated.
Composing this inclusion with the tuple power's structural map proves that the
locus is locally of finite type and separated over `S`. A locally noetherian
base then makes the locus locally noetherian.

`relativeIntegralActionLocusTest` packages that same equalizer as an object of
the original full locally noetherian test category. Its tuple-power premise is
derived from local finite type over the locally noetherian base.
`relativeIntegralActionLocusTestIso` reuses the existing natural isomorphism
between actual integral actions and the restricted lifted Yoneda presheaf of
this object. It retains every morphism of that full category and the same
universe lifts, unit equation, and ordered multiplication equations.

The provenance is internal: these are consequences of the existing equalizer
construction and Mathlib's finite-limit, separatedness, closed-immersion, and
local-finite-type APIs. This module proves no relative endomorphism existence,
rational-to-integral lifting, determinant or Rosati condition, smoothness,
projectivity, or normalized Harris CM representability.
