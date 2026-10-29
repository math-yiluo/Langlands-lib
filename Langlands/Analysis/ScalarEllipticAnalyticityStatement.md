# Interior analytic regularity for coordinate scalar elliptic operators

`Langlands.Analysis.ScalarEllipticAnalyticityStatement E d r` is a
proposition definition. It states the following implication for every
`CoordinateScalarOperator E d r`, set `S : Set E`, and function
`F : E → ℂ`:

- `S` is open.
- Every coefficient of the actual operator `D` is real analytic near
  each point of `S`, expressed by `D.AnalyticCoefficientsOn S`: for every
  `k : Fin (r + 1)` and `w : Fin k.val → Fin d`,
  `AnalyticOnNhd ℝ (D.coefficient k w) S`.
- The actual principal symbol is nonzero at every `x ∈ S` and every
  nonzero real continuous covector `ξ : E →L[ℝ] ℝ`, expressed by
  `D.IsEllipticOn S`.
- `F` is smooth on `S`, expressed by `ContDiffOn ℝ ∞ F S`.
- The actual homogeneous equation holds: `D.action F x = 0` for every
  `x ∈ S`.

The conclusion is `AnalyticOnNhd ℝ F S`: `F` has a convergent real power
series on a neighborhood of each point of `S`.

The `ContDiff` scope makes `∞` the smooth order, the image of
`(⊤ : ℕ∞)` in `ℕ∞ω`. The literal `⊤` at type `ℕ∞ω` would instead
mean analytic order `ω` and would assume the regularity this statement
is intended to conclude. The definition uses `∞`.

The definition quantifies over the original real normed vector space
`E : Type v`, with arbitrary universe `v` and arbitrary natural numbers
`d` and `r`. Its norm, topology and real scalar structure are unchanged.
The finite real basis indexed by `Fin d` belongs to `D`; the statement
adds no separate finite-dimensionality or completeness instance. The
operator action, ordered derivative words and real-covector symbol are
exactly those in the imported
`Langlands.Analysis.CoordinateScalarDifferentialOperator`. In particular,
the action includes all derivative orders from zero through `r` and the
symbol includes no factor of `i`.

The ellipticity assumption is pointwise on `S`. There is no supplied
global lower-bound constant, factorial estimate or analyticity
certificate for `F`. There is no boundary assumption or strong
ellipticity hypothesis. The set need not be bounded or connected.

## Provenance

This is a derived coordinate formulation of the scalar homogeneous
interior specialization of C. B. Morrey and L. Nirenberg, *On the
analyticity of the solutions of linear elliptic systems of partial
differential equations*, Communications on Pure and Applied Mathematics
10 (1957), 271–290. The complete registered original is
`provided-17e51270c6d50eab8ff7b4142058b4ec69474b21e75225ec9952a95784e8229f`,
SHA-256
`61c74249e27625fd25cb0a33d3c77d90ab6b5306fc9bccddc7a6d5314229f915`,
retained as
`literature/Morrey-Nirenberg - On the analyticity of the solutions of linear elliptic systems of partial differential equations (1957).pdf`.
One-based PDF page 1 is printed page 271.

Section 1, equations (1.4)–(1.5), printed page 273 / PDF page 3,
defines general linear elliptic systems with complex coefficients and
nonvanishing highest-order determinant on nonzero real covectors. For a
single scalar equation the determinant is the scalar principal symbol.
Section 5, printed pages 287–290 / PDF pages 17–20, treats interior
analytic regularity for analytic coefficients. Its local argument uses
the uniform homogeneous bound (5.2), the Fourier estimate of Lemma 5.1,
cutoff estimates and a frozen-coefficient induction yielding the
factorial derivative estimate (5.5). Lemma 2.3 and its corollary,
printed pages 276–277 / PDF pages 6–7, supply the passage from such
estimates to analyticity. The present statement takes zero right side
and assumes smoothness from the outset. More precisely, (5.5), printed
page 288 / PDF page 18, bounds the factorially normalized weighted
L² derivative seminorms by `M λ^p`; removing the normalization gives
factorial derivative bounds on smaller balls.

The boundary Theorem A, printed page 274 / PDF page 4, assumes a
strongly elliptic system and zero Dirichlet data on an analytic portion
of the boundary, and concludes analytic extension across that boundary.
Section 5 addresses the interior problem under general ellipticity;
the present formulation uses that interior result. The paper's full
mixed-order systems are outside this scalar statement.

## Comparisons and proof obligations

The original uses Euclidean coordinates and monomials in partial
derivatives. The imported operator uses the given norm on `E`, a finite
basis of actual vectors, ordered derivative words and real iterated
Fréchet derivatives. A proof must construct the continuous linear
coordinate equivalence, compare dual norms, and identify the word sum
with the corresponding classical mixed partial operator on smooth
functions. This includes grouping ordered words with the same
multi-index and summing their coefficients. The imported coefficient
carrier does not prove these comparisons.

The source works locally with a uniform symbol bound. A proof of this
pointwise formulation must obtain such a bound near each point, using
coefficient continuity, compactness of a finite-dimensional covector
unit sphere and symbol homogeneity. The Fourier, cutoff,
frozen-coefficient factorial, Sobolev and Taylor-convergence arguments
remain proof obligations. No source comparison or estimate is proved
by this file.

The source assumes positive total differential order. The present
statement also includes `r = 0` and `d = 0`. For positive dimension and
`r = 0`, the intended elementary proof reduces ellipticity to a
nonzero zero-order coefficient and the homogeneous equation to
`F = 0` on the open set. For `d = 0`, the given empty basis makes `E`
the zero space, and the intended proof uses analyticity of functions
on that space. These are additional proof cases, not consequences
formalized here.

## Status

The Lean file defines the proposition only. It proves no analytic
regularity, coordinate comparison, local uniform bound or degenerate
case, and supplies no Cartan-polynomial specialization or automorphic
growth theorem.

Worker 94 authored the shared draft. Worker 347 checked the cited
original and expanded the quantifier, provenance and scope documentation.
