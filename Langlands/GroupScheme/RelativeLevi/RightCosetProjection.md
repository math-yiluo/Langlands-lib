# Actual right-coset projections from subgroup multiplication

This internal construction is derived from the Library's actual subgroup
multiplication and its pointwise inverse coordinates. It works over any base
scheme and requires no field, reductivity, normality or smoothness hypothesis.

Let `l : L → P` and `r : U → P` be group-scheme homomorphisms for which
the scheme multiplication `U × L → P` is an isomorphism.
`RelativeLevi.rightCosetProjection l r` is its inverse followed by projection
to `U`. It is a morphism of schemes over the base; a homomorphic quotient
is not asserted.

The theorem `rightCosetProjection_fibers` proves that two points `g, h`
have the same image precisely when `g⁻¹h` factors through `l`, on every
relative test scheme. In the forward direction, the inverse coordinates
write `g = u a` and `h = u b`, so `g⁻¹h = a⁻¹b` is in `L`. Conversely,
if `h = g z` with `z` in `L`, multiplication changes only the second
coordinate. Both directions take place on the original test scheme and
use the exact multiplication isomorphism.

The Library's `isIso_subgroupMultiplication_reverse_iff` also permits this
construction when an isomorphism `L × U → P` is initially given. The module
does not assert representability or a torus structure for a further quotient.
