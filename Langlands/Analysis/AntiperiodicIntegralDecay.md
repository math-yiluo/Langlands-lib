# Integrals against antiperiodic and oscillating functions

Module `Langlands.Analysis.AntiperiodicIntegralDecay`, namespace
`Langlands.Analysis.AntiperiodicIntegralDecay`. It proves a finite-difference form of
integration by parts on a finite-dimensional real normed space `E` with a translation invariant
measure `mu` that is finite on compact sets.

## Contents

- `forwardDiff v h` is the forward difference `Δ_v h(y) = h(y) − h(y + v)`.
- `norm_iterate_forwardDiff_le`: for `h` of class `C^k` with `‖D^k h‖ ≤ M` everywhere,
  `‖Δ_v^k h(y)‖ ≤ ‖v‖^k M`. The proof is by induction on `k`. The `(k−1)`-st derivative of
  `Δ_v h` is the difference of two translates of `D^{k−1} h`
  (`iteratedFDeriv_sub_apply`, `iteratedFDeriv_comp_add_right`). The mean value inequality
  (`Convex.norm_image_sub_le_of_norm_fderiv_le`) and `norm_fderiv_iteratedFDeriv` bound that
  difference by `‖v‖ M`.
- `iterate_forwardDiff_eq_zero_of_notMem`: `Δ_v^k h` vanishes outside the `k‖v‖`-thickening of
  the support of `h`, because `Δ_v^k h(y)` only involves the values `h(y + j v)`, `j ≤ k`.
- `integral_mul_eq_half_forwardDiff` and `integral_mul_eq_iterate_forwardDiff`: if
  `Φ(y + v) = −Φ(y)`, translation invariance gives `∫ h(y + v) Φ(y) = −∫ h Φ`. Hence
  `∫ h Φ = ½ ∫ (Δ_v h) Φ` and, for continuous `h` with compact support and continuous `Φ`,
  `∫ h Φ = 2^{−k} ∫ (Δ_v^k h) Φ`.
- `norm_integral_mul_le_of_antiperiodic`: with `‖Φ‖ ≤ A` on the `1`-thickening `S` of the
  support of `h` and `k‖v‖ ≤ 1`, `‖∫ h Φ‖ ≤ (‖v‖/2)^k M A mu(S)`.
- `norm_integral_mul_le_of_phase`: if `Φ(x + s v₀) = e^{i s Y} Φ(x)` for all real `s` and
  `Y ≠ 0`, take `v = (π / Y) v₀`, so that `Φ(y + v) = −Φ(y)`. When `k π ‖v₀‖ ≤ |Y|` this gives
  `‖∫ h Φ‖ ≤ (π ‖v₀‖ / (2|Y|))^k M A mu(S)`.
- `norm_integral_mul_le_of_bound`: the trivial bound `‖∫ h Φ‖ ≤ A ∫ ‖h‖`.
- `exists_norm_integral_mul_one_add_pow_le`: for `h` of class `C^k` with compact support and a
  direction `v₀` there is `K` with `‖∫ h Φ‖ (1 + |Y|)^k ≤ K A` for every continuous `Φ` with the
  phase law above, `0 ≤ A` and `‖Φ‖ ≤ A` on `S`. The phase estimate covers `|Y| ≥ max(kπ‖v₀‖, 1)` and
  the trivial bound covers the rest.

This is the decay of the Fourier transform of a smooth compactly supported function, written for
integrands that are only quasi-periodic along one direction. The method replaces derivatives of
the integrand by differences of the smooth factor; no differentiability of `Φ` is used.
