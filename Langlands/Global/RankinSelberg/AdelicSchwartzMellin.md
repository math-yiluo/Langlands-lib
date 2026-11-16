# Mellin convergence from the adelic theta estimates

This internal helper is derived from the published theta bound and the two
Siegel-region integration estimates in `EqualAnalyticRegions`. It concerns
rank-one theta kernels on the rational quotient of the actual adelic general
linear group. No Iwasawa integration identity is assumed here.

In rank one the chamber spread is zero, so the constant function has every
chamber decay order with central exponent zero. The theta bound supplies an
arbitrarily large negative power on the region of determinant norm at least one.
On the region of determinant norm below one, use the fixed order
`[F : Q] + 1`. The real inequality `sigma > 3`, together with `[F : Q] >= 1`,
then satisfies the small-norm region estimate. Adding the two integrals gives
the claimed finiteness. The constant `3` is sufficient and is not claimed
to be optimal.

The helper also identifies the integral of any measurable rational-invariant
kernel on the idele fundamental domain with its rational quotient integral,
scaled by the inverse slab volume. It uses the published fundamental-domain
formula for the quotient Haar measure and the definition of `ideleMeasure`.

For rank one, nonzero rational rows are explicitly identified with field
units. Thus `thetaNorm_one_eq_tsum` rewrites the theta norm as the sum of the
norms of the last-row evaluations at all principal translates of an idele.
The determinant weight is invariant under those translates. The published
`lintegral_idele_unfold` and the nonnegative sum/integral interchange then give
`lintegral_lastRow_rpow_eq`: the full-idele Mellin integral equals the normalized
quotient theta integral. The slab volume is positive and finite, so the previous
bound proves `lintegral_lastRow_rpow_lt_top` for every continuous dominated
rank-one row function when `sigma > 3`. The integration variable is the actual
`Points F 1`, and the measure is the Library's normalized `ideleMeasure F`.
No product-coordinate or Whittaker-quotient convergence claim is made here.
