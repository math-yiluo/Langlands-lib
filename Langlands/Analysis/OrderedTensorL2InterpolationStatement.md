# L² interpolation for complete ordered derivative tensors

`Langlands.Analysis.OrderedTensorL2InterpolationStatement d r` defines a
proposition on the actual space `V = EuclideanSpace ℝ (Fin d)`. It uses
the standard orthonormal basis `e = EuclideanSpace.basisFun (Fin d) ℝ`,
the canonical `volume` measure on `V`, and Mathlib's extended `L²` norm
`eLpNorm · 2 volume`.

For a function `F : V → ℂ` and an order `m : ℕ`, write

`TₘF(x) = sqrt(∑ w : Fin m → Fin d, ‖(D^m F)(x)(e_{w 0}, …, e_{w (m-1)})‖²)`,

where `D^m F` is exactly `iteratedFDeriv ℝ m F`. Each ordered word `w`,
including words with repeated letters, is counted once. Repeated
directions therefore keep their ordered multiplicities. The tensor norm
is not replaced by the operator norm of the multilinear map
`D^m F (x)`. The name `Tₘ` only explains the expressions in the
proposition; no separate definition is exported. The order `r` tensor
uses the same expression as the published
`Langlands.Analysis.ConstantCoefficientEllipticL2EstimateStatement`.

The proposition asserts the following. Let `k ≤ r` be a natural number,
let `ε > 0` be real, and let `F : V → ℂ` satisfy `ContDiff ℝ ∞ F` and
`HasCompactSupport F`. Then

`eLpNorm (TₖF) 2 volume ≤ ENNReal.ofReal (ε^(r-k)) · eLpNorm (TᵣF) 2 volume + ENNReal.ofReal ((ε⁻¹)^k) · eLpNorm F 2 volume`.

In conventional notation this is

`‖TₖF‖₂ ≤ ε^(r-k) ‖TᵣF‖₂ + ε^(-k) ‖F‖₂`.

The exponent `r - k` is natural number subtraction, which is exact
because `k ≤ r`. Both coefficients are positive reals placed into
`ENNReal` by `ENNReal.ofReal`. All three norms are extended nonnegative
reals. They are finite for smooth compactly supported `F`, but the
statement does not pass to real projections.

Here `∞`, in the opened `ContDiff` scope, is the smooth order obtained
from `(⊤ : ℕ∞)` in `ℕ∞ω`. Literal `⊤` at type `ℕ∞ω` would instead mean
analytic order `ω`. Smooth compactly supported functions are the
intended test functions.

There is no hypothesis on `d` or `r`, no dimension-dependent constant,
and no Fourier transform hypothesis. The scale `ε` is arbitrary.

## Degenerate cases

All `d r : ℕ` and all `k ≤ r` are included.

- At `k = 0` there is one empty word and `T₀F(x) = ‖F x‖`. The
  inequality becomes `‖F‖₂ ≤ ε^r ‖TᵣF‖₂ + ‖F‖₂`.
- At `k = r` the inequality becomes
  `‖TᵣF‖₂ ≤ ‖TᵣF‖₂ + ε^(-r) ‖F‖₂`.
- At `d = 0` and `m > 0` there are no words, so `TₘF = 0`. At
  `d = 0` and `m = 0` the empty word is still present.

These cases hold with the actual definitions and need no separate
hypothesis.

## Provenance and normalization

This is an internal derived statement for the scalar elliptic
regularity route. It does not transcribe a theorem from the literature.
The intended proof is as follows. Each step below is a proof obligation
for a successor. This file proves none of them.

1. For real `t ≥ 0`, `ε > 0` and `k ≤ r`,
   `t^k ≤ ε^(r-k) t^r + ε^(-k)`.
   If `εt ≤ 1`, then `t^k = ε^(-k) (εt)^k ≤ ε^(-k)`. If `εt ≥ 1`,
   then `(εt)^k ≤ (εt)^r`, so `t^k ≤ ε^(r-k) t^r`. The constant is one
   in both cases.
2. A smooth compactly supported `F` is a Schwartz function. Mathlib's
   Fourier transform on a real inner product space is
   `𝓕F(ξ) = ∫ exp(-2πi ⟪x, ξ⟫) F(x) dx` with canonical volume.
   Differentiation in direction `e_j` multiplies `𝓕F` by `2πi ξ_j`.
   The word `w` therefore gives the multiplier
   `(2πi)^m ∏ j : Fin m, ξ (w j)`.
3. Expanding the `m`-th power of `∑ j : Fin d, |ξ j|²` gives the exact
   ordered frequency tensor identity
   `∑ w : Fin m → Fin d, ∏ j : Fin m, |ξ (w j)|² = ‖ξ‖^(2m)`.
4. Interchanging the finite sum with the integral and applying
   Plancherel to each word gives
   `‖TₘF‖₂ = ‖(2π‖ξ‖)^m 𝓕F‖₂`.
5. Apply step 1 at `t = 2π‖ξ‖`, multiply by `|𝓕F(ξ)|`, and use the
   `L²` triangle inequality. Then step 4 at orders `k` and `r`, and
   Plancherel for `F` itself, give the displayed estimate.

The factor `2π` belongs to Mathlib's Fourier normalization. It is
included in `t` and introduces no extra constant, because step 1 holds
for every `t ≥ 0`. With this normalization and canonical volume,
Plancherel is an exact isometry; for Schwartz functions Mathlib states
it as `SchwartzMap.integral_norm_sq_fourier`. Step 3 is an exact
identity, so no constant comes from comparing the complete ordered
tensor with `‖ξ‖^m`. The proposition itself mentions no Fourier
transform. With the unitary convention whose derivative multiplier is
`i ξ_j`, the same argument at `t = ‖ξ‖` gives the same estimate.

## Scope

The Lean file defines only this proposition. It proves no
interpolation, Plancherel or multiplier result. Cutoff estimates,
variable coefficients, local coefficient freezing, absorption of lower
order terms, factorial estimates, analyticity and automorphic growth
are separate obligations.

Worker 94 authored the statement and initial exposition. Worker 990
checked the statement and the intended derivation, and expanded the
exposition for publication.
