# Canonical Euclidean scalar regularity and its coordinate reduction

This module defines two propositions (`def`s returning `Prop`) in the
namespace `Langlands.Analysis`. Both use the unchanged published
`CoordinateScalarOperator` from
`Langlands.Analysis.CoordinateScalarDifferentialOperator` and the unchanged
published `ScalarEllipticAnalyticityStatement` from
`Langlands.Analysis.ScalarEllipticAnalyticityStatement`. Neither proposition
is proved here.

## The canonical Euclidean assertion

`CanonicalEuclideanScalarEllipticAnalyticityStatement d r`, for arbitrary
`d r : ℕ`, states the following for every operator
`D : CoordinateScalarOperator (EuclideanSpace ℝ (Fin d)) d r`, every set
`S : Set (EuclideanSpace ℝ (Fin d))` and every function
`F : EuclideanSpace ℝ (Fin d) → ℂ`. Suppose:

1. `D.basis = (EuclideanSpace.basisFun (Fin d) ℝ).toBasis`. This is the
   canonical orthonormal basis of real Euclidean space, viewed as a real
   linear basis. By Mathlib's `EuclideanSpace.basisFun_apply`, its vector
   with index `i` is `EuclideanSpace.single i 1`.
2. `S` is open.
3. `D.AnalyticCoefficientsOn S`: every actual coefficient
   `D.coefficient k w`, for `k : Fin (r + 1)` and
   `w : Fin k.val → Fin d`, is real analytic near each point of `S`.
4. `D.IsEllipticOn S`: at every `x ∈ S`, the actual principal symbol
   `D.principalSymbol x ξ` is nonzero for every nonzero real continuous
   covector `ξ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ`.
5. `ContDiffOn ℝ ∞ F S`: `F` is smooth on `S`.
6. `D.action F x = 0` for every `x ∈ S`: the full homogeneous equation
   holds, with every derivative order from `0` through `r`.

Then `AnalyticOnNhd ℝ F S`: `F` has a convergent real power series near
each point of `S`.

Apart from premise 1, the premises and the conclusion are those of
`ScalarEllipticAnalyticityStatement (EuclideanSpace ℝ (Fin d)) d r`,
with the same expressions. The canonical assertion therefore restricts the
published one, at the Euclidean space, to operators whose basis is the
standard one. This restriction is evident from the two definitions; no
theorem relating them is stated here.

With the basis fixed, the action is

`∑ k, ∑ w, D.coefficient k w x * iteratedFDeriv ℝ k F x (fun j => e (w j))`,

where `e i = EuclideanSpace.single i 1`. For `F` smooth near `x`, the
iterated derivative evaluated on these standard basis vectors is the mixed
partial derivative of `F` in standard coordinates along the indices
`w 0, …, w (k - 1)`; this identification is explanatory and is not
formalized here. The symbol is
`∑ w : Fin r → Fin d, D.coefficient (Fin.last r) w x * ∏ j, (ξ (e (w j)) : ℂ)`,
a polynomial in the coordinates `ξ (e i)` of the covector, with no factor
of `i`.

Conventions:

- `EuclideanSpace ℝ (Fin d)` carries Mathlib's `L²` norm, its topology and
  its real scalar structure. Openness, analyticity, smoothness and
  continuity of covectors refer to these.
- With `open scoped ContDiff`, `∞` is the smooth order, the image of
  `(⊤ : ℕ∞)` in `ℕ∞ω`. It is not the analytic order `ω`.
- Every `d` and `r` is allowed, including `d = 0`, where the space is the
  zero space, and `r = 0`.
- No uniform symbol bound, boundedness or connectedness of `S`, factorial
  estimate or analyticity certificate for `F` is assumed. The coefficients
  are arbitrary complex-valued functions on the Euclidean space.

## The transport implication

`EuclideanScalarEllipticAnalyticityTransportStatement E d r`, for a real
normed space `E : Type v` in an arbitrary universe `v` and arbitrary
`d r : ℕ`, is the implication

`CanonicalEuclideanScalarEllipticAnalyticityStatement d r →
  ScalarEllipticAnalyticityStatement E d r`.

The premise uses the same `d` and `r` as the conclusion. The conclusion is
the published generic proposition on `E` with its original norm, topology
and real scalar structure, applied to every operator on `E` with its own
actual finite basis. No finite-dimensionality or completeness instance, no
new norm on `E`, no uniform-ellipticity premise and no solution certificate
is introduced.

## Intended proof of the implication

The implication is not proved here. A later proof is expected to proceed
as follows. Let `D` be an operator on `E` with basis `b`. Because `E` has a
finite real basis, it is a finite-dimensional real normed space, so the
linear equivalence `φ : E → EuclideanSpace ℝ (Fin d)` with
`φ (b i) = EuclideanSpace.single i 1` is a continuous linear equivalence.
The pulled-back operator has the canonical basis and coefficients
`D.coefficient k w ∘ φ.symm`. The proof then transports:

- openness of `S` to its image `φ '' S`;
- coefficient analyticity, by composition with the continuous linear map
  `φ.symm`;
- ellipticity, since `ξ ↦ ξ ∘ φ.symm` is a bijection from the nonzero
  real continuous covectors on `E` to those on the Euclidean space, and
  the pulled-back symbol at `φ x` on `ξ ∘ φ.symm` equals
  `D.principalSymbol x ξ`;
- smoothness of `F` to smoothness of `F ∘ φ.symm`;
- the equation, since the iterated derivative of `F ∘ φ.symm` at `φ x`,
  evaluated on the vectors `φ (b i)`, equals the iterated derivative of `F`
  at `x` evaluated on the vectors `b i`, so the pulled-back action at
  `φ x` equals `D.action F x`.

The canonical assertion then gives analyticity of `F ∘ φ.symm` near each
point of `φ '' S`. Composing with `φ` gives `AnalyticOnNhd ℝ F S`. This is
ordinary linear change of coordinates. Every lower-order term and the full
action are kept.

## Provenance

Both propositions are derived interfaces. The published
`ScalarEllipticAnalyticityStatement` is a coordinate formulation of the
scalar homogeneous interior specialization of C. B. Morrey and
L. Nirenberg, *On the analyticity of the solutions of linear elliptic
systems of partial differential equations*, Communications on Pure and
Applied Mathematics 10 (1957), 271–290, registered as
`provided-17e51270c6d50eab8ff7b4142058b4ec69474b21e75225ec9952a95784e8229f`
(SHA-256
`61c74249e27625fd25cb0a33d3c77d90ab6b5306fc9bccddc7a6d5314229f915`). Its
Markdown records the source locators and remaining comparisons. In
section 1, (1.4)–(1.5), printed page 273 / PDF page 3, the original works
with functions of real variables `x = (x₁, …, x_ν)` and with operators that
are polynomials in `∇ = (∂/∂x₁, …, ∂/∂x_ν)`; ellipticity is nonvanishing of
the highest-order determinant at real vectors `ξ ≠ 0`. The canonical
assertion fixes that coordinate setting, with the standard basis. It still uses ordered
derivative words and real iterated Fréchet derivatives rather than
multi-indices; grouping words with the same multi-index remains a proof
obligation of the regularity argument. The transport implication is
internal: it is linear algebra and the chain rule, not a literature
theorem.

The split separates the analytic argument from the change of coordinates.
Analytic estimates can be proved for the canonical Euclidean assertion.
A separate proof of the transport implication then gives the generic
statement. That transport proof is not a proof of the canonical
regularity premise.

## Status

The Lean file defines the two propositions only. It proves no analytic
regularity, coordinate transport, comparison between the two assertions
or degenerate case.

Worker 116 wrote the shared draft, including both Lean definitions.
Worker 1099 expanded the Markdown documentation for review.
