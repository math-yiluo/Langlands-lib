# Uniform value and first-order bounds for the real compact probe

## Definitions

For an `O(n)`-finite standard section `f` of the real block list `ds`:

* `CompactBound f R`: `‖f(x)‖ ≤ R` for every orthogonal matrix `x`;
* `CompactRightDifferenceBound f D`: `‖f(x k) - f(x)‖ ≤ D ‖k - 1‖` for all orthogonal
  `x, k`, where `‖k - 1‖` is the operator norm of the matrix `k - 1`.

## Statement

`RealCompactProbeBoundsStatement`: for every rank `r + 1` and block list `ds` there are
`M`, `C ≥ 0` and `E ≥ 0` such that for every standard section `f`, orthogonal `x`,
opposite-cell coordinate vector `z` and `R`, `D ≥ 0` with `CompactBound f R`:

* `‖dualSection f x (oppositePoint z)‖ ≤ C R (1 + ‖z‖)^M`;
* if moreover `CompactRightDifferenceBound f D`, then
  `‖dualSection f x (oppositePoint z) - f(x)‖ ≤ E (R + D) ‖z‖ (1 + ‖z‖)^M`.

Here `dualSection f x` is the dual compact probe of `RealCompactDualProbe` and
`oppositePoint z` is the point of the opposite cell with coordinates `z`
(`RealOppositeCompactChart`).

## Proof

`realCompactProbeBounds` proves the statement. On the opposite cell the dual section is the
scalar extension factor times the probe at the compact factor:
`dualSection f x (oppositePoint z) = oppositeScalar s z · probe f x (oppositeCompact z)`, with
`s` the shifted negated position exponents (`extension_oppositePoint`).

* The probe is a finite average with sign weights of norm one, so `CompactBound f R` bounds it
  by `R` (`norm_probe_le`), and the polynomial growth of the scalar factor
  (`realOppositeScalarGrowth`) gives the first estimate.
* For the difference, `probe f x k - f(x)` is an average of `f(k⁻¹ y) - f(y)`
  (`norm_probe_sub_le`). Left translation by `k⁻¹` is right translation by the conjugate
  `y⁻¹ k⁻¹ y`, and compactness of `O(n)` gives a constant `J` with
  `‖y⁻¹ k⁻¹ y - 1‖ ≤ J ‖k - 1‖` uniformly in `y`. Hence the right difference bound controls
  the probe difference by `D J ‖k - 1‖`.
* Near the origin (`‖z‖ < ρ`), the local Lipschitz estimates of `realOppositeCompactChart`
  bound `‖oppositeScalar s z - 1‖` and `‖oppositeCompact z - 1‖` by `L ‖z‖`; writing
  `σ F - y = (σ - 1) F + (F - y)` gives a bound by a constant times `(R + D) ‖z‖`.
* Far from the origin (`‖z‖ ≥ ρ`), `1 ≤ ‖z‖ / ρ`, and the value estimate for the dual section
  plus `‖f(x)‖ ≤ R` bounds the difference by `(C + 1) ρ⁻¹ R ‖z‖ (1 + ‖z‖)^M`.

The constants depend only on the rank and on `ds`. This is the real counterpart of the
Library's `ComplexCompactProbeBounds`; it supplies the estimates of the approximate identity
in `RealWhittakerApproximateIdentity`.
