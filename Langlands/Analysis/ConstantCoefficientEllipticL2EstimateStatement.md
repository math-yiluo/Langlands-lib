# The scalar constant-coefficient elliptic L² estimate

`Langlands.Analysis.ConstantCoefficientEllipticL2EstimateStatement d r`
defines a proposition on the actual space
`V = EuclideanSpace ℝ (Fin d)`. It uses the standard orthonormal basis
`e = EuclideanSpace.basisFun (Fin d) ℝ`, its Euclidean norm and canonical
`volume` measure.

An array `a : (Fin r → Fin d) → ℂ` supplies constant complex
coefficients for every ordered derivative word of length `r`. With no
factor of `i`, its real-frequency symbol is

`pₐ(ξ) = ∑ w : Fin r → Fin d, a w · ∏ j : Fin r, (ξ (w j) : ℂ)`.

For every real `c > 0` satisfying
`c · ‖ξ‖^r ≤ ‖pₐ(ξ)‖` at every `ξ : V`, the statement asserts the
following estimate for every `F : V → ℂ` with
`ContDiff ℝ ∞ F` and `HasCompactSupport F`.

Here `∞`, in the `ContDiff` scope, is the smooth order obtained from
`(⊤ : ℕ∞)` in `ℕ∞ω`. Literal `⊤` at type `ℕ∞ω` would instead mean
analytic order `ω`. Smooth compactly supported functions are the
intended test functions.

Write

`LₐF(x) = ∑ w : Fin r → Fin d, a w · (D^r F)(x)(e_{w 0}, …, e_{w (r-1)})`,

and let the real scalar function `TᵣF` be

`TᵣF(x) = sqrt(∑ w : Fin r → Fin d, ‖(D^r F)(x)(e_{w 0}, …, e_{w (r-1)})‖²)`.

Here `D^r F` is exactly `iteratedFDeriv ℝ r F`. Every ordered word,
including repeated letters, is counted once. The conclusion is

`eLpNorm (TᵣF) 2 volume ≤ ENNReal.ofReal (c⁻¹) · eLpNorm (LₐF) 2 volume`.

Both sides are extended nonnegative real numbers. In particular,
the statement does not replace an infinite norm by its real projection.
It uses a concrete sum of squares of actual scalar derivatives, rather
than an arbitrary seminorm or an assumed multiplier representation.
The names `pₐ`, `Lₐ` and `Tᵣ` above explain the expressions in the
proposition; no separate definitions with these names are exported.

## Relation to coordinate scalar operators

In the standard basis, `Lₐ` is the top-order part of the action from
`Langlands.Analysis.CoordinateScalarDifferentialOperator`, with constant
top coefficients `a` and all lower coefficients zero. The principal
symbol is its real-covector symbol after identifying a Euclidean vector
`ξ` with the covector `v ↦ ⟪v, ξ⟫`. This comparison is not proved in
this statement file. Transport from an arbitrary finite basis and
original norm, and passage to variable coefficients, remain separate
proof obligations.

## Source and derived formulation

The source is C. B. Morrey and L. Nirenberg, *On the analyticity of the
solutions of linear elliptic systems of partial differential equations*,
Communications on Pure and Applied Mathematics 10 (1957), 271–290.
The complete registered original is
`provided-17e51270c6d50eab8ff7b4142058b4ec69474b21e75225ec9952a95784e8229f`,
SHA-256
`61c74249e27625fd25cb0a33d3c77d90ab6b5306fc9bccddc7a6d5314229f915`,
retained as
`literature/Morrey-Nirenberg - On the analyticity of the solutions of linear elliptic systems of partial differential equations (1957).pdf`.
One-based PDF page 1 is printed page 271.

Section 2, equation (2.1), printed page 275 / PDF page 5, defines
the tensor norm as the square root of the sum of squared absolute
values of all ordered components. Section 5 uses the homogeneous
symbol lower bound (5.2), printed page 287 / PDF page 17. Its
homogeneous constant-coefficient system (5.6), Lemma 5.1 and
equations (5.7)–(5.8), printed page 288 / PDF page 18, give an
L² estimate using the Fourier transform.

The source treats systems on a ball, with the function vanishing in
a neighborhood of the boundary, and denotes its estimate constant
by `K₁`. The present proposition is a derived scalar, globally
compactly supported formulation. Enclosing the support in a larger
ball supplies the intended comparison with the source's local
formulation. It does not transcribe the source's system constant as
`c⁻¹`.

The intended scalar argument for the displayed constant `c⁻¹` uses
Plancherel and the ordered tensor identity

`∑ w : Fin r → Fin d, ∏ j : Fin r, |ξ (w j)|² = ‖ξ‖^(2r)`.

Each side comes from expanding the `r`-th power of
`∑ k : Fin d, |ξ k|²`. Together with the assumed scalar symbol bound,
this yields the exact inverse constant. These identities and the
estimate are proof obligations, not results proved in this file.

## Fourier normalization

The original on printed page 288 / PDF page 18 takes
`(2π)^(-d/2) ∫ exp(-i x·ξ) F(x) dx`, so its derivative multiplier is
`i ξ_j` and (5.8) substitutes `iξ` in the homogeneous operator.

Mathlib's Fourier transform on a real inner product space takes
`∫ exp(-2πi ⟪x, ξ⟫) F(x) dx` with canonical volume. Consequently a
derivative in direction `e_j` contributes `2πi ξ_j`, and the
homogeneous action contributes `(2πi)^r pₐ(ξ)`. The absolute factor
`(2π)^r` occurs on both sides of the equal-order estimate and
cancels. The symbol in the hypothesis deliberately contains neither
`i` nor `2π`. The proof must establish the multiplier formula,
Plancherel, integrability and all finite-sum interchanges under the
stated smoothness and compact-support assumptions.

## Degenerate cases and status

All `d r : ℕ` are included. At `r = 0` there is one empty word:
the symbol is its coefficient, the action is multiplication by that
coefficient, and `T₀F = ‖F‖`. At `d = 0` and `r > 0` there are no
words, so the displayed tensor and action expressions are zero.
At `d = r = 0` the empty word is still present. A proof must handle
these cases with the actual definitions.

The Lean file defines only this proposition. It proves no Fourier
estimate, local cutoff estimate, variable-coefficient regularity,
analyticity or automorphic growth.

Worker 94 authored the statement and initial exposition. Worker 116 identified
the smooth-order notation defect in the first draft. Worker 88 checked the
revised statement against the cited original and prepared this publication.
