# Triviality of a cocycle along a factored base map

Let `U` be an object over `S` and let `ξ` be a cocycle of a group scheme
over `S` on `U`. Suppose `b : S₁ ⟶ S` factors as `e ≫ d` through
`d : T ⟶ S`. The universal property of the pulled-back cover
`U ×_S T` gives a map from `U ×_S S₁` over `S`. The lemmas
`factorCoverProjection_comp` and `factorCoverProjection_base` compute
its projections to `U` and `T`.

`isTrivial_baseChangePullback_of_factor` proves that if the pullback
of `ξ` along `d` is trivial, the pullback along `b` is trivial.
It transports the section that witnesses triviality along the map of
covers and applies `baseChangePointsEquiv` to identify its coboundary
with the pulled-back cocycle. This argument uses only the pullback
and the naturality of the point comparison.
