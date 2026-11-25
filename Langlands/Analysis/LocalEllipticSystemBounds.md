# A local weighted estimate for finite elliptic systems

This internal estimate extends the scalar cutoff argument to a finite family
of smooth functions satisfying \(D u_i=\sum_j A_{ij}u_j\), where all components
use the same scalar elliptic operator of order \(r>0\) and \(A\) is constant.
The output is one ball and a sequence of finite constants, chosen before
the solution family. On that ball each weighted derivative seminorm is
bounded by its constant times a common bound for the seminorms of orders
less than \(r\).

The proof uses `coordinateScalarFrozenDerivativeEstimate` for the
differentiated action with the principal coefficients frozen at the center.
It takes weighted \(L^2\) seminorms, estimating every lower-order term with
its missing radius weight. Constant linear combinations bound the full
action by weighted seminorms of order \(p\), below the order \(p+r\) being
estimated. The constant-coefficient Fourier estimate and
`exists_factorial_weighted_recursion` yield the cutoff recurrence. The proof
removes its factorial normalization and shrinks the ball so the top-order
error costs at most half of the leading term of that recurrence. Compact
containment gives finiteness before absorption. Strong induction on the
derivative order gives the stated constants.

The absorption step is the public lemma `absorbs_half`: in `ℝ≥0∞`, if
`X ≠ ⊤` and `X ≤ ofReal (1 / 2) * X + Y`, then `X ≤ ofReal 2 * Y`. Its
proof passes to real numbers, which is possible because `X` is finite; when
`Y = ⊤` the bound is immediate.

The finiteness before absorption is the public lemma `weightedSeminorm_lt_top`:
for `0 ≤ R` and `G` continuous on `closedBall x₀ R`, every weighted seminorm
`ballWeightedSeminorm G x₀ R m` is finite. `G` is bounded on the compact closed
ball, hence in `L²` of the finite restricted measure, and each weight
`(R - ρ) ^ m` with `R / 2 ≤ ρ < R` is at most `R ^ m`.
