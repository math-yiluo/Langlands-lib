# Nonvanishing of the pairing along a standard parabolic subgroup

Lean module: `Langlands.Representation.Archimedean.RealLeviNonvanishing`.

This module is part of the proof of `RealStandardLanglandsQuotientStatement` (module
`RealLargeLanglandsQuotientReduction`). It
states and proves `Langlands.Archimedean.RealLeviNonvanishingStatement` (proof
`realLeviNonvanishing`). It is the last of three modules (`RealLeviPairing`, `RealLeviBump`,
`RealLeviNonvanishing`) for the nonvanishing step of the single-shot Langlands-quotient
argument. No literature statement is claimed and nothing is cited; the provenance is internal
("derived"). Unprefixed names below are in the namespace
`Langlands.Archimedean.RealLeviNonvanishing`.

The pairing `Θ(u, h)` is the left side of the conclusion of `RealLeviLimitStatement`. There it
vanishes when all matrix coefficients of `(u, h)` vanish. The statement here says that `Θ(u, ·)`
is not identically zero on the standard module, provided a certain integral over the compact
Levi subgroup, the value at `X = 0` of the inner integrand, is nonzero.

## Notation

As in `RealLeviPairing.md` and `RealLeviBump.md`: `sz : Fin c → ℕ`, `N = ∑_i sz_i`,
`K_M = ∏_i O(sz_i)` with the product `Measure.pi (fun i => haarK (sz i))` of the normalized Haar
measures, `diag(κ) = blockDiagGL sz κ`, `n̄(X) = lowerGL sz X` for `X : Coord sz → ℝ`,
`c_Z F = coeffs (zeroModes (slots ds N)) F 1` (the iterated mode-`0` Fourier coefficient over the
rotations of the induction blocks of `ds`, evaluated at `1`), and
`psi(u, h)(κ, X) = c_Z(x ↦ u(x diag(κ)) h(x n̄(X) diag(κ)))` (`RealLeviPairing.psi`).
`ω` and `β(X) = ω(n̄(X))` are as in `RealLeviBump`.

## The statement

`RealLeviNonvanishingStatement`: assume `RealLeviChartIntegrableStatement`. Let `c : ℕ`,
`sz : Fin c → ℕ` and `ds : List RealBlock` with `realRank ds = ∑_i sz_i = N`, such that

1. `realPositionBlockExponent ds q ≤ realPositionBlockExponent ds p` for all positions
   `p ≤ q` in `Fin N`, and
2. `realPositionBlockExponent ds q < realPositionBlockExponent ds p` for all positions with
   `cls sz p < cls sz q`.

Let `u` be in `kFiniteFunctions (principalSeries ℝ N (dualChar (realPositionCharacter ds)))
(unitaryCompact ℝ N)` and `f` in `kFiniteFunctions (realStandardModule N ds)
(unitaryCompact ℝ N)`. If

`∫_{K_M} c_Z(x ↦ u(x diag(κ)) f(x diag(κ))) dκ ≠ 0`,

then there is `h` in `kFiniteFunctions (realStandardModule N ds) (unitaryCompact ℝ N)` with

`∫_{K_M} ∫_{Coord sz → ℝ} c_Z(x ↦ u(x diag(κ)) h(x n̄(X) diag(κ))) dX dκ ≠ 0`.

The hypotheses 1 and 2 are those of `RealLeviLimitStatement`, and the double integral is its
left side, `RealLeviPairing.theta (slots ds N) u h`.

## Proof outline

Write `F(X) = ∫_{K_M} psi(u, f)(κ, X) dκ`. The hypothesis says `F(0) ≠ 0`.

1. For every `m : ℕ`, `RealLeviBump.exists_bump_standard` gives an `O(N)`-finite vector `f_m` of
   the standard module with `f_m(g) = ω(g)^m f(g)`.
2. `ω` is invariant under left and right multiplication by `∏_i O(sz_i)` (embedded block
   diagonally). The torus elements of the induction slots lie in that group because the
   induction blocks of `ds` lie inside the blocks of `Q` (hypothesis 2). Hence
   `ω(τ_θ n̄(X) diag(κ)) = β(X)` and `psi(u, f_m)(κ, X) = β(X)^m psi(u, f)(κ, X)` (`psi_bump`).
   By Fubini, `Θ(u, f_m) = ∫_X β(X)^m F(X) dX` (`theta_bump`).
3. If `Θ(u, h) = 0` for every `h`, then `∫ β^m F = 0` for every `m`. `F` is integrable
   (`RealLeviPairing.integrable_psi_prod`, which uses `RealLeviChartIntegrableStatement`) and
   continuous (`continuous_integral_psi`). `β` is continuous with `0 < β ≤ 1`, `β(0) = 1` and
   bounded by a constant `< 1` outside every ball around `0` (`RealLeviBump.exists_gap`). The
   concentration lemma then gives `F(0) = 0`, a contradiction.

## Results

**Concentration** (section `Concentration`).

* `concentration`: let `E` be a proper normed additive group with a Borel measure `μ` that is
  positive on open sets and finite on compact sets. Let `β : E → ℝ` be continuous with
  `0 ≤ β ≤ 1`, `β(0) = 1`, and such that for every `δ > 0` some `q < 1` bounds `β` on
  `{‖X‖ ≥ δ}`. If `F : E → ℂ` is integrable, continuous at `0`, and
  `∫ β(X)^m F(X) dμ = 0` for every `m : ℕ`, then `F(0) = 0`. Proof: with `a = F(0) ≠ 0` and
  `φ = Re(ā F)`, `φ(0) = |a|² > 0`. Choose a ball `B` around `0` on which `φ > φ(0)/2` and
  `β > q'`, where `q' = (1 + max(q, 0))/2` and `q` bounds `β` outside the ball of radius `δ` on
  which `φ > φ(0)/2`. Then pointwise `β^m φ ≥ q'^m (φ(0)/2 · 1_B - r^m |φ|)` with
  `r = max(q, 0)/q' < 1`. Integrating, `∫ β^m φ ≥ q'^m (φ(0)/2 · μ(B) - r^m ∫|φ|) > 0` for large
  `m`, while `∫ β^m φ = Re(ā ∫ β^m F) = 0`.

**The bump vectors in the pairing** (section `Bump`).

* `psi_bump`: under hypothesis 2, if `f'(g) = ω(g)^m f(g)` for all `g` (with `u`, `f`, `f'`
  continuous), then `psi(u, f')(κ, X) = β(X)^m psi(u, f)(κ, X)`.
* `continuous_integral_psi`: `X ↦ ∫_{K_M} psi(u, h)(κ, X) dκ` is continuous for continuous `u`,
  `h` (`RealLeviPairing.continuous_psi`, compactness of `K_M`).
* `theta_bump`: under `RealLeviChartIntegrableStatement` and `RealLeviPairing.Admissible sz ds`
  (hypotheses 1, 2 and the rank condition), `Θ(u, f') = ∫_X β(X)^m F(X) dX`.
* `exists_theta_ne_zero`: if `∫_{K_M} psi(u, f)(κ, 0) dκ ≠ 0`, then `Θ(u, h) ≠ 0` for some
  `O(N)`-finite vector `h` of the standard module (steps 1–3).

`realLeviNonvanishing` applies `exists_theta_ne_zero`, using `n̄(0) = 1`
(`RealLeviLimit.lowerGL_zero`) to identify `psi(u, f)(κ, 0)` with the integrand of the
hypothesis.
