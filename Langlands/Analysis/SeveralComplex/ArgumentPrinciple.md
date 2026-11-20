# A weighted argument principle

Module `Langlands.Analysis.SeveralComplex.ArgumentPrinciple`, namespace
`Langlands.Analysis.SeveralComplex`.

## Setting

`f : ℂ → ℂ` is complex differentiable on an open set `U ⊆ ℂ` containing the closed disc
`closedBall c R` with `R > 0`, and `f` has no zero on the boundary circle `sphere c R`. Write
`D = divisor f (closedBall c R)` for Mathlib's divisor of `f` on the closed disc
(`MeromorphicOn.divisor`): a function `ℂ → ℤ` that vanishes off the closed disc and records
orders of vanishing on it.

## Results

- `analyticOrderAt_ne_top_of_ne_zero_on_sphere`: for every `u` in the closed disc,
  `analyticOrderAt f u ≠ ⊤`, i.e. `f` does not vanish identically near `u`.
- `divisor_closedBall_eq_analyticOrderNatAt`: for `u` in the closed disc, `D u` is the order
  of vanishing `analyticOrderNatAt f u` of `f` at `u` (as an integer).
- `divisor_closedBall_ne_zero_iff`: `D u ≠ 0` if and only if `u ∈ ball c R` and `f u = 0`.
- `divisor_closedBall_support_finite`: `D` has finite support. (This holds for every `f`; it
  is Mathlib's local finiteness of divisors on the compact closed disc.)
- `circleIntegral_logDeriv_smul` (**weighted argument principle**). For every complex Banach
  space `F` (`CompleteSpace F`) and every `φ : ℂ → F` complex differentiable on `U`,

  `∮ t in C(c, R), (deriv f t / f t) • φ t = (2πi) • ∑ᶠ u, (D u : ℂ) • φ u`.

  By the previous items the right-hand side is `2πi` times the sum of `ord_u(f) · φ(u)` over
  the zeros `u` of `f` in the open disc. With `φ = 1` this is the classical argument principle
  (the integral counts the zeros of `f` in the disc with multiplicity); with `φ(t) = t^j` it
  gives the power sums of the zeros.

## Proofs

- Finite order: the closed disc is convex, hence preconnected, and `f` is analytic on a
  neighbourhood of it (`DifferentiableOn.analyticOnNhd`, since `U` is open). Its order at the
  boundary point `c + R` is `0` because `f(c + R) ≠ 0`; by
  `AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected` the order is finite everywhere on
  the disc.
- Divisor as order: `AnalyticOnNhd.divisor_apply` identifies `D u` with the untopped
  meromorphic order, which for an analytic function with finite order is
  `analyticOrderNatAt f u`. This order is nonzero exactly when `f u = 0`
  (`AnalyticAt.analyticOrderAt_ne_zero`), and a zero in the closed disc cannot lie on the
  circle, so it lies in the open disc. Off the closed disc `D` is `0` by definition.
- Argument principle. Let `S` be the finite support of `D` (the zeros in the open disc) and
  `P(x) = ∏_{u ∈ S} (x - u)^{D u}`. Mathlib's `MeromorphicOn.extract_zeros_poles` gives `g`
  analytic and nowhere zero on the closed disc with `f = P · g` on the disc outside a
  codiscrete set. At each point `t` of the circle, both `f` and `P · g` are analytic, they
  agree at points of the open disc accumulating at `t`, so by the identity theorem
  (`AnalyticAt.frequently_zero_iff_eventually_zero`) they agree on a neighbourhood of `t`.
  Hence the logarithmic derivatives agree at `t`, and by `logDeriv_mul`, `logDeriv_fun_prod`
  and `logDeriv_fun_zpow`,

  `f'(t)/f(t) = ∑_{u ∈ S} D(u) (t - u)⁻¹ + g'(t)/g(t)` for `t` on the circle.

  Multiplying by `φ(t)` and integrating: the term `(g'/g) • φ` is holomorphic on a
  neighbourhood of the closed disc, so its integral vanishes (Cauchy's theorem,
  `DiffContOnCl.circleIntegral_eq_zero`); each remaining term gives
  `D(u) • ∮ (t - u)⁻¹ • φ(t) dt = D(u) • 2πi • φ(u)` by Cauchy's integral formula
  (`DifferentiableOn.circleIntegral_sub_inv_smul`, `u` in the open disc). The finite sum over
  `S` equals the `finsum` over all `u` since `D` vanishes off `S`.

## Provenance

Internal. The weighted argument principle is a standard result of one-variable complex
analysis (the residue theorem applied to `φ f'/f`), which Mathlib does not contain in this
form. It is a supporting lemma for the proof of
`Langlands.Analysis.Meromorphic.MeromorphicContinuationAnalyticComplementStatement`
(Bernstein–Lapid, Theorem 3.3): there the power sums `∑ ord_u(f) u^j a(u)` of a holomorphic
family over the zeros of a holomorphic function in a disc, expressed as circle integrals, are
used to reduce the number of variables. The Lean proof follows the route described above and
uses only Mathlib.
