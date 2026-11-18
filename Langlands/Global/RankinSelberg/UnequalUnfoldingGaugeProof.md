# The gauge integrability premises of the unequal-rank unfolding

Module `Langlands.Global.RankinSelberg.UnequalUnfoldingGaugeProof`, namespace
`Langlands.Global.RankinSelbergGlobal`.

The theorem `unequalUnfoldingGauge` proves the unchanged published
proposition `UnequalUnfoldingGaugeStatement.{u}`. Its universe and all of its
hypotheses are retained.

## What is proved

Write `n = r + 1` and `m = t + 1`. For every number field `F : Type u` whose
additive adelic quotient `AdeleQuotient F` is compact, all `r t : ℕ` with
`h : t < r`, every actual cuspidal operator realization `T` of rank `n` and
every actual cuspidal operator realization `T'` of rank `m`, the theorem
proves both premises of `UnequalUnfoldingReductionStatement`:

- G, `WhittakerGaugeIntegrable F h T T'`. There is a real `C ≥ 0` such that,
  for every standard additive character `ψ`, all vectors `v`, `v'` and every
  complex `s` with `Re s > C`, the function
  `h ↦ W(diag(h, I_{n-m})) φ'(h) |det h|^{s-(n-m)/2}` is integrable on the
  rational unipotent quotient `N_m(F) \ GL_m(𝔸)`. Here
  `W = cuspWhittaker F T ψ v` and `φ' = cuspFunction F T' v'` is the cusp
  form of the smaller group.
- G', `DualWhittakerGaugeIntegrable F h T T'`. There is a real `C ≥ 0` such
  that, for every standard `ψ`, all `v`, `v'` and every `s` with `Re s > C`,
  the real function
  `h ↦ (∫_x ‖W̃(rect(h, x) w')‖ dx) · ‖φ̃'(h)‖ · ‖|det h|^{s-(n-m)/2}‖`
  is integrable on the same rational unipotent quotient
  `N_m(F) \ GL_m(𝔸)`. The inner integral is the integral of the absolute
  value over the `(n-m-1) × m` adelic matrices (`rectangleMeasure`). Here
  `W̃ = dualFunction W`, `w' = unfoldingWeyl F h`,
  `rect = rectangularPoint F h`, and `φ̃' = dualFunction F m φ'` is the dual
  cusp form of the smaller group, not a Whittaker function.

In each premise the threshold `C` is chosen before the standard character,
both vectors and `s`, so it is uniform over them.

## Provenance

Source: J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004), §2.2
(source `cogdell-2004-analytic-theory-gln`).

- G is the absolute convergence, for `Re(s) » 0`, of the integral over
  `N_m(k) \ GL_m(𝔸)` displayed at the foot of printed p.205 (PDF p.208). It
  is asserted at the head of p.206 (PDF p.209): "This integral is absolutely
  convergent for Re(s) » 0 by the gauge estimates of [22, Section 13] and
  this justifies the interchange." The Lean premise additionally requires
  the threshold to be uniform over standard characters and vectors.
- G' is a derived premise of the Library, not a claim printed by Cogdell.
  It is the dual premise before unipotent averaging. It concerns the
  rational quotient `N_m(F) \ GL_m(𝔸)` and the smaller dual cusp form `φ̃'`,
  with the absolute value integrated over the rectangular matrices. Its
  motivation is the dual unfolded integral `Ψ̃(s; W, W')` on printed p.207
  (PDF p.210). There the `h`-integral runs over `N_m(𝔸) \ GL_m(𝔸)`, the
  `x`-integral runs over `M_{n-m-1,m}(𝔸)`, and the smaller factor is a
  Whittaker function. Cogdell states that "As before, Ψ̃(s; W, W') is
  absolutely convergent for Re(s) » 0." The Library's
  `dual_unfolding` (module `UnfoldingDual`) uses G' as its integrability
  hypothesis. It averages over `N_m(F) \ N_m(𝔸)` to pass from the rational
  quotient integral with `φ̃'` to the absolutely convergent dual Whittaker
  integral. As with G, the Lean premise requires a threshold uniform over
  standard characters and vectors.

## Proof

The proof is the one-line composition

`unequalGaugeReduction unequalPadGauge unequalRectGauge`

of three published Library theorems:

1. `unequalGaugeReduction : UnequalGaugeReductionStatement.{u}` (module
   `UnequalGaugeReduction`). This is the implication
   `UnequalPadGaugeStatement.{u} → UnequalRectGaugeStatement.{u} →
   UnequalUnfoldingGaugeStatement.{u}`. It removes the smaller group's cusp
   form from G and its dual cusp form from G'. A power bound
   `‖φ'(g)‖ ≤ C' |det g|^β` and the same bound for `φ̃'` come from
   `CuspCentralBound`. The exponent `β` is chosen before the vector. The
   threshold is shifted to `max 0 (C₀ + (n-m)/2 - β)`, where `C₀` is the
   threshold of the corresponding gauge bound. The integrals over the
   rational quotient `N_m(F) \ GL_m(𝔸)` are then compared with the
   Whittaker-quotient integrals in the two gauge bounds.
2. `unequalPadGauge : UnequalPadGaugeStatement.{u}` (module
   `UnequalPadGaugeProof`). For each realization `T` and rank `t < r` it gives
   one nonnegative threshold. Above it, `∫ ‖W(pad h)‖ |det h|^σ` over
   `N_m(𝔸) \ GL_m(𝔸)` is finite, uniformly in the standard character and the
   vector.
3. `unequalRectGauge : UnequalRectGaugeStatement.{u}` (module
   `UnequalRectGaugeProof`). It gives the corresponding bound for an
   iterated integral over `N_m(𝔸) \ GL_m(𝔸)`. The integrand is the dual
   Whittaker function, right translated by the unfolding Weyl element and
   evaluated at the rectangular points. The inner integral is over the
   rectangular matrices.

Every hypothesis of the two bound statements is the corresponding hypothesis
of the target, so the reduction applies with no further premise. The proof
adds no hypothesis on the number field, ranks, realizations, characters or
vectors. The analytic arguments and their literature sources are documented
in the Markdown of the imported modules. This module is an internal
composition of those published results.
