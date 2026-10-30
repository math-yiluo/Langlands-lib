# Proof of the shell generating integrals of finite functions

`Langlands.RankinSelberg.finiteFunctionShellSeries :
FiniteFunctionShellSeriesStatement.{uF}` proves the published proposition
`Langlands.RankinSelberg.FiniteFunctionShellSeriesStatement` from the module
`Langlands.Representation.RankinSelberg.FiniteFunctionShellSeriesStatement`.
The universe `uF` is arbitrary. The theorem's type is the whole Library
statement: it keeps every prime `p` with `Fact p.Prime`, field
`F : PadicField.{uF} p`, supplied realization `T : F.TopologicalData`, function
`η` with its continuity and finite-dimensional translation-span hypotheses, and
it adds no hypothesis. The module introduces no other declaration.

The proof installs the statement's instances in the statement's order:
`T.topology`, `T.valuativeRel`, `T.localField`, `borel F.Carrier` with its
`BorelSpace` witness, and `borel F.Carrierˣ` with its `BorelSpace` witness. It
then introduces the statement's let-bound measure
`μ = localMultiplicativeHaar F.Carrier` and integral units
`K = integralUnits (ValuativeRel.valuation F.Carrier).integer` unchanged.

## Published results used

The proof reuses three published proofs by their Lean names.

- `Langlands.RankinSelberg.valuationShellIntegration`
  (module `Langlands.Representation.RankinSelberg.ValuationShellIntegrationProof`)
  for the same `p`, `F`, `T`. It supplies a unit `π` with `T.ord π = 1`, the
  shell identity `S 0 = K` for `S n = {a | T.ord a = n}`, and, for `n = 0`,
  that `S 0` is compact, measurable and of measure one. It also supplies the
  integrability criterion: a continuous `f` is integrable for `μ` exactly when
  `n ↦ ∫ u in K, ‖f (π ^ n * u)‖ ∂μ` is summable over `ℤ`. Finally it supplies
  the identity: for continuous integrable `f`, the shell integrals
  `n ↦ ∫ u in K, f (π ^ n * u) ∂μ` are summable and their sum is `∫ a, f a ∂μ`.
- `Langlands.HarmonicAnalysis.finiteTranslationOrbit`
  (module `Langlands.HarmonicAnalysis.FiniteTranslationOrbitProof`), applied to
  the unit group `F.Carrierˣ`, the given `η` with its two hypotheses, and
  `t = π`. It gives a `LinearRecurrence ℂ` named `E` and a real `B ≥ 1` such
  that `n ↦ η (π ^ ((n : ℤ) + k) * a)` solves `E` for every `k : ℤ` and unit `a`.
  For the compact set `K` it gives `C > 0` with
  `‖η (π ^ n * u)‖ ≤ C * B ^ n.natAbs` for all `n : ℤ` and `u ∈ K`.
- `Langlands.HarmonicAnalysis.schwartzBruhatValuationBounds`
  (module `Langlands.HarmonicAnalysis.SchwartzBruhatValuationBoundsProof`),
  applied to each test function `Φ`. It gives `L : ℤ`, `N : ℕ` and `CΦ > 0` with
  `L ≤ N` and `‖Φ x‖ ≤ CΦ` for all `x`. It also gives `Φ a = 0` for every unit
  `a` with `T.ord a < L`, and `Φ a = Φ 0` for every unit `a` with
  `N ≤ T.ord a`.

The witnesses of the statement are this `π`, `E` and `B`. They are chosen
before `Φ`, since they depend only on the field data and `η`. The witnesses
`L` and `N` for a test function `Φ` are those of
`schwartzBruhatValuationBounds`.

## Orders on the integral units

From `S 0 = K`, every `u ∈ K` has `T.ord u = 0`. The published `ord_mul` (both
factors are nonzero), `Units.val_zpow_eq_zpow_val` and `ord_zpow` give
`T.ord (π ^ n * a) = n + T.ord a` for every `n : ℤ` and unit `a`. Hence
`T.ord (π ^ n * u) = n` for `u ∈ K`.

For each `m : ℤ`, the function `u ↦ η (π ^ m * u)` is continuous. Since `K` is
compact and measurable, Mathlib's `ContinuousOn.integrableOn_compact'` makes it
integrable on `K`. The needed finiteness on compact sets comes from the
published Haar instance for `μ`.

## Lower support bound

Let `c n = ∫ u in K, Φ (π ^ n * u) * η (π ^ n * u) ∂μ`, as in the statement.
If `n < L`, every `u ∈ K` has `T.ord (π ^ n * u) = n < L`, so `Φ (π ^ n * u) = 0`
and the integrand vanishes on `K`. Mathlib's
`setIntegral_eq_zero_of_forall_eq_zero` gives `c n = 0`.

## Recurrent tail

If `N ≤ n`, every `u ∈ K` has `T.ord (π ^ n * u) = n ≥ N`, so
`Φ (π ^ n * u) = Φ 0`. By `setIntegral_congr_fun` and `integral_const_mul`,
`c n = Φ 0 * ∫ u in K, η (π ^ n * u) ∂μ`.

Fix `j : ℕ`. The orbit recurrence at `k = N` and `a = u` says, pointwise in `u`,

```text
η (π ^ ((j + E.order : ℕ) + N) * u)
  = ∑ i : Fin E.order, E.coeffs i * η (π ^ ((j + i : ℕ) + N) * u).
```

Integrating over `K` and exchanging the finite sum with the integral
(`integral_finsetSum`, using the integrability above, then
`integral_const_mul`) gives the same recurrence for the orbit integrals
`∫ u in K, η (π ^ m * u) ∂μ`. Every index `(j + E.order) + N` and `(j + i) + N`
is at least `N`. Multiplying by `Φ 0` and using the previous paragraph turns
it into

```text
c ((j + E.order : ℕ) + N) = ∑ i : Fin E.order, E.coeffs i * c ((j + i : ℕ) + N),
```

which is `E.IsSolution (fun j => c (j + N))`. Nothing is assumed about
`E.order` or `Φ 0`: order zero gives an empty sum, and `Φ 0 = 0` gives a zero
tail.

## Integrability and the bilateral sum

Fix `z ≠ 0` with `B * ‖z‖ < 1`. Let
`f a = Φ a * η a * z ^ (T.ord a)` on `F.Carrierˣ`, the statement's integrand.
It is continuous: `Φ` is continuous, composed with the continuous coercion of
units; `η` is continuous by hypothesis; and `a ↦ z ^ (T.ord a)` is the
composition of the published continuous order map `continuous_ord_units` into
the discrete integers with a function on a discrete space.

For `u ∈ K`, `T.ord (π ^ n * u) = n`, so
`f (π ^ n * u) = Φ (π ^ n * u) * η (π ^ n * u) * z ^ n`. Hence
`∫ u in K, f (π ^ n * u) ∂μ = c n * z ^ n` (`integral_mul_const`), and
`‖f (π ^ n * u)‖ = ‖Φ (π ^ n * u)‖ * ‖η (π ^ n * u)‖ * ‖z‖ ^ n`
(`norm_zpow`).

Let `h n = ∫ u in K, ‖f (π ^ n * u)‖ ∂μ`. Each `h n` is nonnegative.

- If `n < L`, the factor `Φ (π ^ n * u)` vanishes on `K`, so `h n = 0`.
- For `m : ℕ` and `u ∈ K`, the two bounds give
  `‖f (π ^ m * u)‖ ≤ CΦ * (C * B ^ m) * ‖z‖ ^ m = CΦ * C * (B * ‖z‖) ^ m`.
  Since `μ K = 1`, Mathlib's `norm_setIntegral_le_of_norm_le_const` gives
  `h m ≤ CΦ * C * (B * ‖z‖) ^ m`.

So `h` is summable over `ℤ` (`Summable.of_nat_of_neg`). On nonnegative indices
it is dominated by the convergent geometric series with ratio
`0 ≤ B * ‖z‖ < 1` (`summable_geometric_of_lt_one`, `Summable.of_nonneg_of_le`).
On negative indices `-m` it vanishes once `m ≥ |L| + 1`, since then `-m < L`
(`summable_of_ne_finset_zero`).

The integrability criterion of `valuationShellIntegration` now gives
`Integrable f μ`, the first conclusion. Its integral identity gives
summability of `n ↦ ∫ u in K, f (π ^ n * u) ∂μ` and
`∫ a, f a ∂μ = ∑' n, ∫ u in K, f (π ^ n * u) ∂μ`. Rewriting each shell integral
as `c n * z ^ n` (`summable_congr`, `tsum_congr`) gives the second and third
conclusions. A negative `L`, `N = 0`, `Φ 0 ≠ 0` and the zero function `η` need
no separate case.

## Provenance and attribution

Worker 277 wrote this proof; no other draft was reused. It follows the route
described in the statement's Markdown, which labels the statement a derived
internal step. That Markdown cites Jacquet–Piatetski-Shapiro–Shalika,
*Rankin-Selberg Convolutions* (1983), printed pp. 391–392, display (6), and
Jacquet–Piatetski-Shapiro–Shalika, *Automorphic forms on GL(3) I* (1979),
§(2.2), for finite functions. The analytic ingredients come from the three
published proofs listed above, whose own authors are recorded in their
Markdown. This module only combines them.

## Checks

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiled
the module with no errors or warnings. Inspecting
`Langlands.RankinSelberg.finiteFunctionShellSeries` showed universe parameter
`uF` and only the axioms `propext`, `Classical.choice` and `Quot.sound`. The
module contains no `sorry`, `admit` or new axiom. Compilation does not
establish acceptance. Independent review, the Lake build and the exact-target
check remain required.
