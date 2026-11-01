# Self-products of specified cartesian squares

This internal construction applies to a specified square of schemes, rather
than requiring its upper-left scheme to be definitionally the chosen
categorical pullback. It is derived from Mathlib pullback universal properties
and the Library's definitions of actual abelian self-products and unit axes.
It makes no new literature claim.

Let `p : X → S`, `q : Y → T`, `a : X → Y` and `b : S → T` satisfy
`a ≫ q = p ≫ b`, in arbitrary common universe `u`.
`cartesianSelfProductMap` is the actual map
`X ×_S X → Y ×_T Y` induced by `a` on both factors and `b` on the base.
Its two projection equations are proved directly from the categorical
pullback lift.

`cartesianSelfProductMap_isPullback` assumes the specified original square
is a pullback square and proves that the induced square on self-products is
a pullback square, using their first-factor structure maps to `S` and `T`.
For a cone over the asserted square, the proof lifts its two projections to
`Y` separately through the original pullback square. Their structure maps to
`S` coincide, so they define a map into `X ×_S X`. The two projection
equations verify the cone identities. Uniqueness follows first from the
self-product universal property and then from that of the original square.

For abelian schemes `A` over `S` and `B` over `T`,
`cartesianMumfordProductMap` specializes this construction to their actual
Library self-products. If the carrier map satisfies
`unitSection A ≫ a = b ≫ unitSection B`, the companion theorems prove that
both actual unit axes commute with the self-product map. They use the two
projection equations, the displayed square equality and the unit equation.
No compatibility with addition is assumed or needed for these conclusions.

The construction supplies geometric comparisons for approximation
arguments. It does not descend an abelian scheme or a line bundle, construct
axis trivializations, or establish extension over any base.
