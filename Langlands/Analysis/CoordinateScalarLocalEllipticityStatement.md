# A local uniform lower bound for a scalar elliptic symbol

## The statement

`Langlands.Analysis.CoordinateScalarLocalEllipticityStatement E d r` is a
proposition definition (a `def` returning `Prop`) for a real normed
space `E : Type v` in an arbitrary universe `v` and any `d r : ℕ`. It
uses the published `CoordinateScalarOperator E d r` and its
`principalSymbol` and `IsUniformlyEllipticOn` from
`Langlands.Analysis.CoordinateScalarDifferentialOperator`.

It says: if `0 < r`, then for every operator
`D : CoordinateScalarOperator E d r` and every point `x₀ : E`, the two
hypotheses

1. for every top-order word `w : Fin r → Fin d`, the coefficient
   `D.coefficient (Fin.last r) w : E → ℂ` is continuous at `x₀`, and
2. `D.principalSymbol x₀ ξ ≠ 0` for every nonzero real continuous
   covector `ξ : E →L[ℝ] ℝ`,

imply that some open set `U : Set E` contains `x₀` and satisfies
`D.IsUniformlyEllipticOn U`.

Unfolding the conclusion, there is one real constant `c > 0` with

`c * ‖ξ‖ ^ r ≤ ‖D.principalSymbol x ξ‖`

for every `x ∈ U` and every `ξ : E →L[ℝ] ℝ`, including `ξ = 0`.

## Conventions kept

- `E` keeps its own norm, topology and real scalar structure. `IsOpen`
  and `ContinuousAt` refer to that topology.
- The basis `D.basis`, the coefficient array `D.coefficient` and the
  symbol `D.principalSymbol` are exactly the imported ones. The symbol
  has no factor of `i`.
- `‖ξ‖` is the continuous-dual operator norm for the original norm of
  `E`. The right side is the complex absolute value. No Euclidean or
  coordinate norm replaces either.
- Every dimension `d` is allowed, including `d = 0`, where `E` is the
  zero space.

The statement does not assume continuity of the coefficients of order
below `r`, analyticity of any coefficient, a differential equation or a
solution, a uniform bound at the start, or `d > 0`. Only continuity at
the single point `x₀` is assumed for the top coefficients.

## Provenance

This is an internal statement. It is the standard compactness and
continuity consequence of pointwise ellipticity, applied to the actual
homogeneous symbol defined in the published module and to its proved
homogeneity lemma `principalSymbol_smul`. It is not a transcription of
a theorem in a separate source. It serves as the passage from pointwise
ellipticity (`IsEllipticOn`, as assumed in
`ScalarEllipticAnalyticityStatement`) to the uniform ellipticity used in
Fourier `L²` estimates, such as condition (5.2) of Morrey and Nirenberg
(1957) recalled in the imported module's Markdown.

## Intended proof

These steps are proof obligations; the Lean file proves none of them.

1. The basis `D.basis : Module.Basis (Fin d) ℝ E` makes `E` finite
   dimensional. Its continuous dual `E →L[ℝ] ℝ` is then finite
   dimensional, so its unit sphere `{ξ | ‖ξ‖ = 1}` is compact. It is
   empty when `d = 0`.
2. For fixed `x₀` the map `ξ ↦ ‖D.principalSymbol x₀ ξ‖` is continuous
   (a polynomial in the values `ξ (D.basis i)`). By hypothesis 2 it is
   positive on the sphere, so it has a positive minimum `m` there. If
   the sphere is empty, any `m > 0` works.
3. On the sphere `|ξ (D.basis i)| ≤ ‖D.basis i‖`. So the difference
   `‖D.principalSymbol x ξ - D.principalSymbol x₀ ξ‖` is at most a
   fixed constant times
   `∑ w, ‖D.coefficient (Fin.last r) w x - D.coefficient (Fin.last r) w x₀‖`.
   By hypothesis 1 for the finitely many words `w`, there is a common
   open neighborhood `U` of `x₀` on which this is at most `m / 2` for
   every `ξ` on the sphere. Then `‖D.principalSymbol x ξ‖ ≥ m / 2` on
   `U` times the sphere.
4. For `ξ ≠ 0`, homogeneity (`principalSymbol_smul` with the scalar
   `‖ξ‖⁻¹`) gives `‖D.principalSymbol x ξ‖ = ‖ξ‖ ^ r * ‖D.principalSymbol x (‖ξ‖⁻¹ • ξ)‖
   ≥ (m / 2) * ‖ξ‖ ^ r`.
5. For `ξ = 0`, positive order gives `‖0‖ ^ r = 0`, so the required
   inequality reads `0 ≤ ‖D.principalSymbol x 0‖`. This is the only
   place where `0 < r` is used.

So `c = m / 2` works on `U`.

## Why positive order is required

The hypothesis `0 < r` cannot be dropped. Take `d = r = 0` and the zero
coefficient. Then `E` is the zero space, its only covector is `0`, and
hypothesis 2 holds vacuously. The constant coefficient is continuous,
so hypothesis 1 holds too. The symbol is the zero-order coefficient,
which is `0` everywhere. At `ξ = 0` the uniform bound would require
`c * ‖0‖ ^ 0 = c ≤ 0`, because `‖0‖ ^ 0 = 1`, contradicting `c > 0`. As
`U` must contain `x₀`, no `U` works, so the unrestricted order-zero
version is false.

For order zero, analytic regularity is a separate elementary case of
the unchanged target `ScalarEllipticAnalyticityStatement E d 0`. That
case does not go through this statement, and it is not treated here.

## Intended applications (not formalized here)

- Restriction to a domain. For an open domain `S` with `x₀ ∈ S`, the
  set `U ∩ S` is open, contains `x₀`, and satisfies
  `D.IsUniformlyEllipticOn (U ∩ S)` by the published lemma
  `IsUniformlyEllipticOn.mono`.
- Coefficient continuity from analyticity. If
  `D.AnalyticCoefficientsOn S` and `x₀ ∈ S`, each coefficient is
  analytic at `x₀` and therefore continuous at `x₀`. This supplies
  hypothesis 1.

Neither implication is proved in this file.

## Status

The Lean file defines only the proposition. It proves no local lower
bound, compactness argument, Fourier estimate, analytic regularity,
Cartan-polynomial realization or automorphic growth theorem.

Worker 94 wrote the Lean definition and the first Markdown draft.
Worker 881 revised the Markdown.
