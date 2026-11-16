# Reciprocal generic multipliers and removal of one scalar pole

This is internal algebra and analysis for the explicit finite products in
`RealBlockMultiplier`, reusing the denominator hypotheses already supplied by
`RealBlockMultiplierGeneric`. It has no external source. It constructs no
parameter limit of intertwining operators.

For `a_i = ε + 2i + 1`, `genericSeq ν ε m` is the product of
`(a_i - ν)/(a_i + ν)` over `i < m`. Negating `ν` inverts every factor, so
`genericSeq_neg` proves the reciprocal identity without hypotheses, using the
totalized inverse also at zero. The same identity holds for
`genericMultiplier`, since its reflection sign is its own inverse.
`IsGenericParameter.neg` preserves the two exclusions. With those exclusions,
the forward and opposite generic sequences and multipliers multiply to one.

`analyticAt_genericSeq` requires only that the finitely many denominators
occurring in the chosen coordinate be nonzero. It follows by taking finite
products of analytic quotients.

`regularizedSeq ν ε r m` removes the denominator at index `r`. If `r < m`,
its formula is `(a_r - ν)` times the quotient product over all indices
`i < m` except `r`. Otherwise it is `(a_r + ν) genericSeq ν ε m`.
Away from `ν = -a_r`, `regularizedSeq_eq_mul_genericSeq` identifies it
with `(a_r + ν) genericSeq ν ε m`. The identity needs only `a_r + ν ≠ 0`;
other quotients may use the totalized inverse.

`analyticAt_regularizedSeq` assumes the remaining denominators are nonzero.
They are all nonzero at `ν = -a_r`, because their values are `2(i-r)` for
`i ≠ r`. Thus `analyticAt_regularizedSeq_at_pole` provides an analytic
extension at this root of the scalar product multiplied by its vanishing
linear factor. For `m ≤ r`, its value there is zero.

For `r < m`, splitting off the new factor at `m` gives
`regularizedSeq_succ_of_lt`. At `ν = -a_r`, this proves the sequence
recurrence above `r`. Below `r`, both adjacent regularized values are zero.
At `m = r`, the left recurrence coefficient and the right sequence value
are zero. These three cases prove `regularizedSeq_at_pole_succ`.
If `ε ≥ 0`, every numerator at the pole is the strictly positive real
number `a_i + a_r`. The remaining denominators are nonzero, so
`regularizedSeq_at_pole_ne_zero_iff` says the regularized value is nonzero
exactly when `r < m`.

`regularizedMultiplier` extends this sequence to integer modes using the
same reflection sign as `genericMultiplier`. It equals the generic
multiplier times `a_r + ν` away from the root and is analytic there after
regularization at every fixed mode. For `ε ∈ {0,1}` it is symmetric.
The proved sequence recurrence and the Library reflection-extension theorem
give `isRecurrent_regularizedMultiplier_at_pole`, with recurrence parameter
`1 - a_r`. On the parity class `Even (k-ε)`, its nonzero values are exactly
the modes `a_r < |k|`. This support assertion is restricted to that parity
class.

These statements describe scalar coefficients only. They do not assert
regularity or invertibility of a four-crossing map, or Lie intertwining of
an operator obtained by taking a parameter limit.
