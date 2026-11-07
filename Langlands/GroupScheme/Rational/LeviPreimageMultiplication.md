# Original-Levi multiplication in actual inverse images

This internal helper is a scheme-theoretic consequence of a supplied
two-factor multiplication isomorphism and the universal property of a
group-scheme pullback. Worker 74 implements it for the nested-parabolic
extension task.

Let `t : R → Q`, `n : N → Q`, `s : V → Q` and `nR : N → R` be homomorphisms
over any base scheme, with `nR ≫ t = n`. If multiplication `N × V → Q`
through `n` and `s` is an isomorphism, then multiplication
`N × (R ×_Q V) → R` through `nR` and the actual inverse-image inclusion
is an isomorphism. The scheme `N` is exactly the supplied first factor.
No smoothness, field, surjectivity or section of all of `Q` is assumed.

The proof establishes bijectivity on every relative test scheme and applies
Yoneda. For injectivity, composing two factorizations with `t` and using
the supplied multiplication isomorphism identifies their `N` and `V`
coordinates. Cancellation in `R` identifies their remaining inclusion
coordinates, and the pullback universal property identifies the two
inverse-image points. For surjectivity, decompose the image of any `R` point
using `N × V → Q`. Multiply the point by the inverse of its lifted `N`
coordinate; the residual point and its `V` coordinate determine a point of
the pullback. Their product recovers the original point. This proves the
actual scheme isomorphism on all tests, including nonreduced ones.

`subgroupPreimageMultiplicationIso` packages the proved isomorphism as an
actual isomorphism of schemes over the base. Its forward morphism is exactly
`subgroupMultiplication nR (SubgroupPreimage.inclusion t s)`, as recorded by
`subgroupPreimageMultiplicationIso_hom`.
