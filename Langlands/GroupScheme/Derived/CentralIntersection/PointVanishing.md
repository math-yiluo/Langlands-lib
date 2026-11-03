# Global functions on reduced schemes over an algebraically closed field

Author: Worker 1408.

This internal helper module proves two standard facts about global sections.
They are used by the central intersection finiteness proof. Both are derived
content, proved directly from Mathlib's scheme theory. Namespace:
`Langlands.GroupScheme.CentralIntersection`.

## Vanishing at rational points

`eq_zero_of_forall_appTop_eq_zero`: let `K` be an algebraically closed field,
`X` a reduced scheme and `p : X ⟶ Spec K` locally of finite type. If a global
function `f ∈ Γ(X, ⊤)` satisfies `q.appTop f = 0` for every section
`q : Spec K ⟶ X` of `p` (every `K`-rational point), then `f = 0`.

Proof. `X` is a Jacobson space (`LocallyOfFiniteType.jacobsonSpace`). Since `X`
is reduced, `f = 0` is equivalent to the basic open `D(f)` being empty
(`basicOpen_eq_bot_iff`). Suppose `D(f)` is nonempty. It is open, so it contains
a closed point `x` (`nonempty_inter_closedPoints`). Over an algebraically closed
field, a closed point comes from a rational point `q = pointOfClosedPoint p x`
with `q ≫ p = 𝟙`. The unique point of `Spec K` lies in `q⁻¹(D(f)) = D(q.appTop f)`.
But `q.appTop f = 0` by hypothesis, and the basic open of `0` is empty. This is
a contradiction.

## Idempotents on connected reduced schemes

`eq_zero_or_eq_one_of_isIdempotentElem`: on a connected scheme `X` (the Lean
statement also assumes `X` reduced), every idempotent global function `e` is `0`
or `1`.

Proof. The basic opens `D(e)` and `D(1 - e)` are disjoint, because
`e (1 - e) = 0`. They cover `X`, because in each local ring the images of `e`
and `1 - e` sum to `1`, so one of them is a unit. Hence `D(e)` is clopen, so it
is empty or all of `X`. If it is empty, then `e = 0`. Otherwise `D(1 - e)` is
empty, so `1 - e = 0`. Both conclusions use `basicOpen_eq_bot_iff` on the
reduced scheme `X`.
