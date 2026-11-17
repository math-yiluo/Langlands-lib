# Finite products of unirational schemes over a field

Worker 321. This is a derived geometric helper for the finite-product step in
Milne's *Algebraic Groups* (2017), Corollary 17.92.

`UnirationalFiniteProductsStatement` asserts that, over every field, the property
of being unirational is closed under finite categorical products, including the
empty product. It is a Prop-valued definition in every universe.
`unirationalFiniteProductsStatement` proves this proposition from the explicit
parametrization constructions below. Its provenance is derived from the
published unirational transport, affine-space and pullback-density helpers and
Mathlib's product infrastructure; it does not claim a separate source theorem.

`IsUnirational.tensor` constructs a dense-image morphism to the fibre product
from a nonempty open of finite-dimensional affine space. The two given
parametrizations are tensored. Their source is an open subscheme of the product
of their affine spaces. The latter is isomorphic over the ground field to an
iterated affine space, and hence is unirational by the published coordinate
sum isomorphism.

The map of products is factored into two base changes. Over a field every
structure morphism of schemes is universally open (Mathlib), so the pullback
projections are open maps. The published pullback-density lemma then proves
density of each factor and of their composite. This also explains the separate
`denseRange_tensorHom` result. Nonemptiness of the parametrizing product follows
from surjectivity of a nonempty scheme over the one-point spectrum of a field.
No smoothness, finite type or infinite-field hypothesis is imposed on the targets.

The empty product is parametrized by zero-dimensional affine space mapping onto
`Spec k`. The binary result and invariance under isomorphism give the public
`isUnirational_closedUnderFiniteProducts` instance. Theorems
`isUnirational_of_isLimit_fan` and `isUnirational_pi` expose the corresponding
limiting-fan and chosen-product forms, including the empty family.
