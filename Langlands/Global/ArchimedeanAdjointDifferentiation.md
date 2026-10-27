# Scalar cochain differentiation along compact adjoint curves

This module constructs continuous scalar evaluation of algebraic alternating
cochains in the actual archimedean matrix coordinates and proves the derivative
of that evaluation along compact conjugation curves. It is an internal derived
construction supporting later differentiation of full compact equivariance.

## Parameters and actual objects

Let `K : Type u` be a number field and let `n : ℕ`. The Lie algebras,
`ArchimedeanMatrix K n`, the linear equivalence `realLieAlgebraToMatrix`, and
`standardInfiniteCompact K n` are the published actual mixed real/complex
archimedean objects. Matrix spaces carry their existing finite-dimensional real
normed-space structures. The conjugation convention is
`Ad(g) X = g X g⁻¹`, and the bracket is the matrix commutator.

The coefficient module `V : Type v` has only an additive commutative group and
a complex module structure. The universes `u` and `v` are independent. Fix an
algebraic complex alternating cochain
`f : ComplexLieAlgebra K n [⋀^Fin q]→ₗ[ℂ] V` and a complex linear functional
`ℓ : V →ₗ[ℂ] ℂ`, with any `q : ℕ`, including zero. No topology on `V` or on the
algebraic complexification is required.

## Actual adjoint derivative

`compactCurve_adjoint_deriv` takes a skew-adjoint direction
`Y : compactLieSubalgebra K n`, a real Lie element `X`, and a curve
`c : ℝ → standardInfiniteCompact K n`. Its hypotheses are `c 0 = 1` and
`HasDerivAt` at zero of the actual matrix coordinates of `c`, with derivative
the matrix coordinates of `Y.val`. It proves

\[
\left.\frac{d}{dt}\right|_{0} \operatorname{matrix}
  (\operatorname{Ad}(c(t))X)
  = \operatorname{matrix}([Y,X]).
\]

The proof rewrites the inverse of a compact matrix as its star, applies the
product and star derivative rules, and uses `star Y = -Y` to obtain `YX - XY`.
This is an actual matrix derivative rather than an assumed differential of an
abstract adjoint representation. The theorem accepts any curve with the stated
coordinate derivative; it does not assert curve existence.

## Continuous scalar evaluation and its derivative

`scalarCochainMatrixEvaluation` is a continuous real multilinear map with `q`
inputs in `ArchimedeanMatrix K n` and output in `ℂ`. On a tuple `M`, its value is

\[
\ell\bigl(f((\operatorname{complexify}
  (\operatorname{matrix}^{-1}(M_i)))_i)\bigr).
\]

`scalarCochainMatrixEvaluation_apply` records this formula. Here
`matrix⁻¹` denotes the inverse linear equivalence, not matrix inversion.
The construction postcomposes `f` with `ℓ`, restricts scalars to `ℝ`, and
precomposes each input with the matrix-coordinate inverse followed by
complexification. The private helper `realMultilinear_continuous` proves the
needed continuity: expand each input in a finite real basis, use multilinearity
to express evaluation as a finite sum of products of continuous coordinate
functions times fixed complex values, and apply continuity of finite sums,
finite products and scalar multiplication.

For the same `Y`, `c` and curve hypotheses, and any tuple
`X : Fin q → RealLieAlgebra K n`, `compactCurve_scalarCochain_deriv` proves

\[
\left.\frac{d}{dt}\right|_{0}
  \ell\bigl(f((\operatorname{complexify}
    (\operatorname{Ad}(c(t))X_i))_i)\bigr)
  = \sum_{i\in\mathrm{Fin}(q)}
    \ell\bigl(f(\operatorname{update}
      ((\operatorname{complexify}(X_j))_j)\ i\
      (\operatorname{complexify}([Y,X_i])))\bigr).
\]

The formal conclusion is a real-parameter, complex-valued `HasDerivAt` at zero.
The proof combines the coordinate derivatives using `hasDerivAt_pi`, applies
`ContinuousMultilinearMap.hasFDerivAt` and the scalar chain rule, and rewrites
`linearDeriv_apply` as the finite insertion sum. At degree zero this sum is
empty and the cochain evaluation is constant.

## Provenance and scope

This is an internal construction from the published
`ArchimedeanRelativeAdjoint`, `ArchimedeanAdjoint` and `ArchimedeanLieAlgebra`
objects and Mathlib's finite-basis, multilinear-map and derivative APIs.
The formulas and their proof route are justified directly by those actual
constructions; no identification with an external source definition is claimed.
The module introduces no new axioms or compatibility certificates.

The results supply scalar analytic prerequisites. They do not assert that a
group-equivariant automorphic cochain satisfies infinitesimal equivariance,
that the relative differential is horizontal, or that relative cohomology or
general automorphic coefficient modules have been constructed. Those remain
separate obligations of the global definition branch.
