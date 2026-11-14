# Explicit big-cell factors for opposite quadratic root parameters

This internal calculation derives an actual matrix factorization from the published
`SU3Root.Parameters`, `SU3Root.oppositeEmbedding` and `SU3Root.diagonal` constructions.
It is algebra over an arbitrary field with a specified ring involution and has no
characteristic restriction. It uses no building, torus-filtration or group-property
assumption.

For upper parameters `p` and opposite parameters `q`, let
`t = 1 - p.first * bar(q.first) + p.second * q.second`. When `t` is nonzero,
`oppositeProductUpper` has coordinates
`((p.first - p.second*q.first)/t, p.second/t)` and
`oppositeProductLower` has coordinates
`((q.first - p.first*bar(q.second))/bar(t), q.second/t)`.
Their trace-norm equations follow by clearing denominators and using the two
input trace-norm equations.

`upper_mul_opposite_factorization` states that the product of the upper matrix
of `p` with the opposite matrix of `q` is the product of the opposite matrix
of `oppositeProductLower`, the diagonal matrix with parameter `t`, and the upper
matrix of `oppositeProductUpper`. The implemented proof checks the nine entries,
clears the two nonzero denominators and uses the input trace-norm equations.
This supplies actual factors for later applications of the conditional
`SU3RootOppositeCommutator` diagonal calculation.

`oppositeCommutator_factorization` multiplies these factors on the left
by the inverse of the opposite matrix of `q`, and on the right by the
inverse of the upper matrix of `p`. The resulting factors have parameters
`q⁻¹ * oppositeProductLower` and `oppositeProductUpper * p⁻¹`, with the
same diagonal parameter `t`. The commutator convention is exactly
`opposite(q)⁻¹ * upper(p) * opposite(q) * upper(p)⁻¹`.

The valuation lemmas use any additive valuation into `WithTop ℝ`. When it
is invariant under the involution, lower bounds `r` and `s` on the two
root depths, with `r+s ≥ 0`, give `omega(t-1) ≥ r+s`. The trace-norm
equation supplies the first-coordinate bounds through
`Parameters.first_ge_of_second_ge`; the second-coordinate product has
value at least `2*(r+s)`. The valuation inequality for their sum gives
the claimed bound. If `r+s > 0`, the pivot cannot be zero, since the
value of `-1` is zero.

When either first coordinate is zero, `oppositeProductPivot_sub_one_of_double`
identifies `t-1` exactly with `p.second*q.second`.
`value_oppositeProductPivot_sub_one_of_double` and
`doubleTop_depthA_add_depthA` identify its value with twice the sum of
the two root depths, including infinite values. A finite positive sum
therefore makes `t` nonzero without needing involution invariance.
`exists_oppositeCommutator_factorization_of_double_depth_sum` constructs
the factors and applies the published
`value_diagonal_sub_one_eq_double_of_depth_sum` to obtain the exact
`2r` bound.

These results concern the concrete matrix groups. They do not supply
the coordinate maps into an arbitrary reductive group, comparison with
a supplied apartment, or induced-torus character congruences.
