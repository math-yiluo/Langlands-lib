# Real Tate zeta integrals: convergence and holomorphy

Helper module for the proof of `Langlands.LocalFactor.RealArchimedeanTateStatement`
(see `RealTateProof.md`). Authored by Worker 823. Everything here is a proved lemma
or an auxiliary definition; there are no hypotheses or axioms.

## Definitions

All declarations are in the namespace `Langlands.LocalFactor.RealTate`.

- `integrand f e u x` is `f(x) sgn(x)^e |x|^(u-1)` for `x ≠ 0` and `0` at `x = 0`, where
  `sgn(x)` is written `x / |x|` (as in the Library statement), `e : Fin 2` is the parity and
  `u : ℂ`. It is the Library statement's integrand with `u = s + t`.
- `zeta f e u` is its Lebesgue integral `∫ integrand f e u x dx`, the real Tate zeta
  integral `Z(f, e, u)` against the multiplicative measure `dx/|x|` and the quasicharacter
  `sgn^e |·|^u`.
- `reflect f` is the Schwartz function `x ↦ f(-x)`, built with
  `SchwartzMap.compCLMOfContinuousLinearEquiv` from the negation isometry.

## Results and proofs

- Sign algebra: `sign_sq_eq_one`, `sign_pow_mul_self` (`sgn(x)^e sgn(x)^e = 1` for
  `x ≠ 0`), `sign_mul` (`sgn(xy) = sgn(x) sgn(y)`).
- `integrand_of_pos`, `integrand_of_neg`: on `x > 0` the integrand is the Mellin integrand
  `x^(u-1) f(x)`; on `x < 0` it is `(-1)^e (-x)^(u-1) f(-(-x))`.
- `integrand_const_mul`, `zeta_const_mul`: linearity in a scalar factor.
- `measurable_integrand`: measurability for measurable `f`.
- `isBigO_atTop`, `isBigO_nhdsGT`: a Schwartz function is `O(x^(-a))` at `+∞` for every
  real `a` (from `SchwartzMap.isBigO_cocompact_rpow`) and bounded near `0⁺` (continuity).
- `mellinConvergent`, `differentiableAt_mellin`: by Mathlib's
  `mellinConvergent_of_isBigO_rpow` and `mellin_differentiableAt_of_isBigO_rpow`, the
  Mellin transform of a Schwartz function converges and is complex differentiable at every
  `u` with `0 < Re u`.
- `integrableOn_Ioi`, `integrableOn_Iio`, `integrable_integrand`: for `0 < Re u` the
  integrand is integrable on `(0, ∞)` (Mellin convergence), on `(-∞, 0)` (Mellin
  convergence of `reflect f`, transported by `IntegrableOn.comp_neg_Iio`), hence on `ℝ`
  (the point `0` is harmless because the integrand vanishes there).
- `zeta_eq_mellin`: for `0 < Re u`,
  `Z(f, e, u) = 𝓜(f)(u) + (-1)^e 𝓜(f(-·))(u)`; the integral is split at `0` with
  `intervalIntegral.integral_Iio_add_Ici` and the negative half is reflected with
  `integral_comp_neg_Ioi`.
- `differentiableAt_zeta`, `differentiableOn_zeta`, `analyticAt_zeta`: `u ↦ Z(f, e, u)` is
  holomorphic on the open half-plane `0 < Re u`, because it agrees there with the sum of
  two differentiable Mellin transforms; analyticity follows from
  `DifferentiableOn.analyticAt` on the open half-plane.
- `integrand_mul`, `zeta_eq_sign_mul_zeta_comp_mul` (dilation): for `a ≠ 0`,
  `Z(φ, e, w) = sgn(a)^e |a|^w Z(φ(a ·), e, w)` for every function `φ` and every `w`. The
  proof is the change of variables `x ↦ a x` of `Measure.integral_comp_mul_left`
  together with the multiplicativity of `sgn` and of `|·|^(w-1)` on positive reals.
  This identity holds for all `w` as an identity of Bochner integrals (both sides are `0`
  when the integrals diverge, since the two integrands differ by a nonzero constant).

## Provenance

This is the standard real-place part of Tate's local theory: J. T. Tate, *Fourier analysis
in number fields and Hecke's zeta-functions* (Cassels–Fröhlich 1967, Chapter XV),
section 2.4 (convergence of local zeta integrals for `Re > 0`) and section 2.5 (real
place). The reduction to Mellin transforms is the implementation route chosen here.
