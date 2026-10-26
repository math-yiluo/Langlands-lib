# Smoothness of finite products and the multiplicative group

Authors: Worker 57 (Lean proofs); Worker 522 (documentation and verification).

This module proves smoothness properties of the actual schemes and finite
products constructed in `Langlands.GroupScheme.Products` and
`Langlands.GroupScheme.Multiplicative`. It is an internal consequence of those
constructions and Mathlib's smoothness and categorical limit APIs.

`smooth_of_over_iso` transports smoothness along an isomorphism in `Over S`.
The commuting triangle writes the source structure morphism as the composite
of the underlying isomorphism with the target structure morphism.
`smooth_tensor` proves that the binary product of two smooth schemes over `S`
is smooth: its structure morphism is a pullback projection followed by one of
the smooth structure morphisms. Smoothness is preserved by base change and
composition.

Two private instances show that the property of being smooth over `S` is
closed under empty and binary products. An empty limiting cone has terminal
cone point, hence is isomorphic to the tensor unit of `Over S`, whose structure
morphism is the identity of `S`. For a binary limiting cone, uniqueness of
limits compares it to the tensor product just treated. Mathlib's
`ObjectProperty.IsClosedUnderFiniteProducts.mk'` combines these cases.
`smooth_pi` then applies this closure to `piIsLimit`, the underlying limiting
fan of the actual product of group schemes. Its index type is any finite
type in the base scheme's universe; no nonemptiness is assumed.

`smooth_gm` proves that the actual multiplicative group is smooth over any
scheme `S`. Over `ULift ℤ`, the Laurent polynomial algebra is the localization
of the one-variable polynomial algebra at `Polynomial.X`. Polynomial
smoothness, localization smoothness and composition give smoothness of this
algebra over `ULift ℤ`. The affine spectrum criterion proves smoothness of
`Gm.overSpecZ.hom`. The definition of `Gm S` makes its structure morphism the
pullback of this integral structure morphism, so base change finishes the proof.
