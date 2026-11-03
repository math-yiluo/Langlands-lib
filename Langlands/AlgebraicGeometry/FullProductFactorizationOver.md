# Full-product factorization over a base

This internal adapter compares the scheme sieve in
`Langlands.AlgebraicGeometry.FullProductFactorizationSieve` with the actual
monoidal product in `Over S`. It is derived from the universal properties of
fiber products and the definition of a morphism over `S`, without an external
source assertion.

For `t : T → Y` over `S`, `testProductIso t` identifies the pullback using
`t.left ≫ Y.hom` with the chosen source product `X ⊗ T`; the equality `t.w`
identifies their structural maps. Its projection lemmas show that the
comparison followed by `(X ◁ t).left` is exactly `productMap`.

`exists_over_lift_iff` observes that a scheme factorization of a morphism over
`S` through another morphism over `S` automatically respects `S`. It imposes
no monomorphism assumption. Using this fact and the product comparison,
`mem_iff_over` identifies membership of `t.left` in the full-product sieve
with existence of `q : X ⊗ T → D` such that `q ≫ d = X ◁ t`, the condition
in `ClosedFactorizationLocusStatement`. These comparisons apply to every
scheme test in the arbitrary universe `u`.
