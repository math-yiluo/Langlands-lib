# Integral choices for balanced induction-block crossings

This is internal arithmetic for the explicit crossing and regularization
constructions. It derives balanced normalizations from the integral window in
`RealInducedSwapIntegralReduction`; it uses no additional representation-theoretic
or analytic assertion. The result supplies the arithmetic input to the limiting
intertwiner construction. This module does not itself prove Lie equivariance or
the full swap statement.

For an integer parameter `t` and parity representative `epsilon`, `integerChoice`
selects `some r` when `t = -(epsilon + 2*r + 1)`, and `none` otherwise. Its
validity is proved by casting this integer equation to the complex numbers.
For `epsilon` equal to zero or one, a negative root exists exactly when `t < 0`
and `(t + epsilon) % 2 = 1`. This gives the removed-denominator order. A positive
root of the same parity instead has `integerChoice = none`; the imported
`multiplier_finite_at_positive` then gives finite modes with cutoff `t.toNat`.
The positive and negative root witnesses are constructed by integer division by
two, and the root and parity assertions are proved by integer arithmetic.

Write `p = d.weight.natAbs` and `q = e.weight.natAbs`. If the first constituent
parameter is `-m`, the four parameters, in crossing order, are
`-m`, `p-m`, `q-m`, and `p+q-m`. Their parity representatives are respectively
`(q+1)%2`, `(p+q)%2`, `0`, and `(p+1)%2`. The exponent identities follow by
linear combinations of the first parameter equation; the parity identities
follow directly from `chA`, `chB`, and `pairParity`.

`intervalChoices p q m` applies `integerChoice` to these four pairs of integers.
`intervalNormalization p q m` also selects division by one parameter exactly
when `m < p`, `m < q`, or `m%2 = q%2`. These definitions apply to all natural
inputs, while their validity and order properties retain the hypotheses
`p > 0`, `q > 0`, and `min p q <= m <= max p q`.

Every selected division has the existing `Cancels` certificate. When
`m%2 = q%2`, the final parameter `p+q-m` is a positive root, with cutoff at most
`max p q`. If the parities differ and `m < p`, the `AC` parameter `p-m` is a
positive root with cutoff at most `p`. If the parities differ and `m < q`, the
`BD` parameter `q-m` is a positive root with cutoff at most `q`. The imported
finite-mode cancellation conditions therefore apply, including the endpoints.
No cancellation certificate is required when division is unselected.

The negative-root indicators show that the total removed order is one exactly
when `p < m`, `q < m`, or `m%2 = q%2`, and is zero otherwise. At most one of the
first two inequalities can hold in the interval, and either is counted only
when the parities differ. For the reverse crossing the weights are `q,p` and
the integer is `m' = p+q-m`. This complementary integer stays in the same
interval, its parity match is equivalent to the original one, and its strict
inequalities interchange the removed-order and division tests. Thus the
forward removed order equals the reverse division order and conversely; the
proof concludes by commutativity of addition. This is exactly `Balanced`.

Finally, `IntegralWindow d e m` implies the general interval bound: its upper
bound `2*m <= p+q` implies `m <= max p q`. Nonzero weights give positive `p,q`,
and the reverse first parameter is `-(p+q-m)`. The theorem
`exists_balanced_of_integralWindow` applies the validity construction in both
directions and the balance identity to exhibit `a,b` with
`IsValid d e a`, `IsValid e d b`, and `Balanced a b`. Its unequal-absolute-weight
input matches the consumer's interface; the arithmetic construction also works
when those weights agree.
