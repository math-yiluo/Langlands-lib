# Explicit thickness inequalities in a sorted log-weight chamber

This module is an internal calculation for the compact-difference route
to [`DrinfeldFacetDistinguishedStatement`](DrinfeldFacetDistinguishedStatement.lean).
It is a calculation on real tuples, not an identification of a polytope
with a star in the norm model. That identification, or a different route
to the actual star, is needed to apply it.

Let `l > 0` and consider sorted tuples of `d+1` real weights, indexed
from 0 through `d`. `IsSortedStar l v` says that `v` is nondecreasing
and every adjacent gap `v_(k+1) − v_k` is at most the external gap
`l − (v_d − v_0)`. The additive distance used in this calculation is
the spread of coordinate differences. It is unchanged by translations
of either tuple.

For sorted `u` of width `s = u_d − u_0 < l` and `ε > 0`,
`exists_isSortedStar_iff` identifies the condition that there exists such
a `v` with spread of `u−v` less than `ε`. It is equivalent to the finite
family of strict inequalities

`u_j − u_i + n s < n l + (1+n) ε`, for `0 ≤ i ≤ j ≤ d` and `n = j−i`.

## Proof

For necessity, the spread hypothesis gives `u_j−u_i < v_j−v_i+ε`
and `v_d−v_0 > s−ε`. Summing the adjacent bounds gives
`v_j−v_i ≤ n(l−(v_d−v_0))`. Combining these gives the test.

For sufficiency, take `δ` to be the maximum of 0 and the numbers
`(u_j−u_i+n(s−l))/(1+n)` for all index pairs, using the truncated natural
subtraction `n = j−i`. Reverse pairs contribute nonpositive numbers
and the assumed tests give `δ < ε`. If `s ≤ δ`, take `v_i = u_0`.
Otherwise put `L = l−s+δ` and set

`v_i = max(u_0, max_j (u_j − δ − max(j−i,0) L))`.

As `i` increases by one, every term inside the maximum is nondecreasing
and increases by at most `L`, so `v` has these properties too. The tests
with `δ` give `u_i−δ ≤ v_i ≤ u_i`; at the endpoints the maximum gives
`v_0 = u_0` and `v_d = u_d−δ`. Thus `L = l−(v_d−v_0)` and the adjacent
bounds put `v` in `IsSortedStar l`. The coordinate bands put the spread
of `u−v` at most `δ`.

`not_sortedStarIneq_log_iff` exponentiates the failure of one test for
`u_i = log(w_i)` with positive `w_i`. It becomes the closed monomial
comparison

`exp(n l + (1+n) ε) · (w_i · w_0^n) ≤ w_j · w_d^n`.

This explicit formula provides finite weak inequalities for the
complement, with integer powers; no general projection or elimination
theorem for polyhedra is used.
