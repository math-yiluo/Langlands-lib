# Natural geometric product comparison for etale restriction

Author: Worker 13.

## Scope and conventions

Let `X` and `Z` be schemes in universe `u`, and let `f : Z ⟶ X` be
etale. For `V : X.Etale`, write `f*V` for the actual scheme fiber-product
object constructed by `etaleObjectPullback f`. Write `L` for the functor
`EtalePullback.siteMap f`, which composes structural maps with `f`.
The binary products below are the chosen categorical products on the actual
small etale categories. No finiteness or torsor condition is imposed on `V`.

The module constructs the canonical isomorphism

`L (f*V ×_Z U) ≅ V ×_X L U`

for every `U : Z.Etale`. The isomorphism is natural in both `V` and `U`.
Its input schemes and morphisms, products, fiber products and maps are the
actual Mathlib objects. The etale assumption on `f` makes composition land
in the small etale category of `X`.

## Construction

`etalePullbackProjection` is the first scheme fiber projection, regarded as
a morphism over `X`. `etalePullbackProjection_natural` proves its naturality
by the first-coordinate equation for the actual base-change functor.

`etaleProductPullbackHom` is the product lift whose first coordinate is the
image of the projection to `f*V`, followed by the first fiber projection to
`V`, and whose second coordinate is the image of the projection to `U`.
The two `etaleProductPullbackHom_fst` and `_snd` equations record these maps
on the underlying schemes.

For the inverse, `etaleProductOverBase` regards the scheme underlying
`V ×_X L U` as an etale object over `Z`, using its second projection followed
by the structure map of `U`. The first projection to `V` and this map to `Z`
satisfy the fiber-product relation. Their lift defines
`etaleProductOverBaseFst`, a morphism to `f*V` over `Z`.
`etaleProductOverBaseSnd` is the second projection to `U`.
Their product lift over `Z`, regarded as a morphism over `X`, is
`etaleProductPullbackInv`. Its `_fst` and `_snd` equations identify its two
coordinates.

`etaleProductPullbackIso` proves the two maps are inverse. For the composite
on `L (f*V ×_Z U)`, the proof first regards its underlying scheme map as an
endomorphism over `Z`. Equality follows by the two product projections,
and the projection to `f*V` is checked by the two scheme fiber projections.
The other composite is checked by the two product projections over `X`.
All equalities follow from the product and fiber-product universal properties.

`etaleProductPullbackHom_natural` proves, for arbitrary cover and test-object
morphisms `a : V ⟶ V'` and `b : U ⟶ U'`, the equality

`L.map (prod.map ((etaleObjectPullback f).map a) b) ≫ comparison(V',U')`
`= comparison(V,U) ≫ prod.map a (L.map b)`.

The proof checks the two product coordinates, using naturality of the first
fiber projection for the first coordinate and functoriality for the second.
In particular this covers deck endomorphisms and all morphisms of test objects.

## Provenance and remaining obligations

This is an internal derived geometric prerequisite for comparing actual
associated coefficient sheaves under etale restriction. It is obtained from
the existing `etaleObjectPullback` and `EtalePullback.siteMap` constructions,
Mathlib's actual scheme fiber products, and categorical binary products.
It is not attributed to an additional theorem of Harris or Berkovich.

This module does not construct the sheaf, diagonal-action or invariant-limit
comparisons; those require applying the natural geometric isomorphism to
sheaves and proving compatibility with their actions and limits. It does not
construct inverse image for an arbitrary non-etale base morphism, a Harris
Shimura scheme or level torsor, or a support, trace, uniformization or
cohomological comparison. Those obligations remain separate.
