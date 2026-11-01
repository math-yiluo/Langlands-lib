# Uniqueness of absolutely convergent bilateral spectral coefficients

Authors: Worker 352 (Lean formulation and source verification) and Worker 486
(analytic prerequisite specification and proof rationale).
This module supplies a **statement**, expressed as the
closed proposition definition
`Langlands.RankinSelberg.BilateralSpectralCoefficientUniquenessStatement`.
It is a derived scalar analytic prerequisite. No proof of this proposition
is supplied here.

## Exact statement and conventions

For every natural number `q` with `1 < q` and every pair
`a b : Langlands.HarmonicAnalysis.BilateralLaurentSeries`, assume that there
exists a real number `C` such that for every complex number `s` satisfying
the strict inequality `C < s.re`, all three assertions hold:

1. `Summable (fun m : ℤ => ‖a m * spectralPoint q s ^ m‖)`;
2. `Summable (fun m : ℤ => ‖b m * spectralPoint q s ^ m‖)`;
3. `(∑' m : ℤ, a m * spectralPoint q s ^ m) =
   (∑' m : ℤ, b m * spectralPoint q s ^ m)`.

The conclusion is `a = b` as the original bilateral series. Since
`BilateralLaurentSeries` is the existing type `ℤ → ℂ`, this is equivalent
to equality of every integer coefficient. The real bound may depend on
`q`, `a`, and `b`; it is shared by the two summability assumptions and the
sum equality.

The imported `Langlands.RankinSelberg.spectralPoint` is exactly
`spectralPoint q s = (q : ℂ) ^ (-s)`, using complex exponentiation.
The subsequent power `spectralPoint q s ^ m` is an **integer** power in
`ℂ`, including every negative integer. The assumption `1 < q` implies
`0 < q`, so the existing `spectralPoint_ne_zero_of_pos` ensures that
these spectral points are nonzero.

The coefficient type imposes no support restriction. The statement
assumes no lower or upper support bound, finite support, recurrence,
rational representation, coefficient equality, or Fourier-extraction
formula. The norms in the hypotheses are norms of the actual weighted
terms, rather than norms of the unweighted coefficient family.
Completeness of `ℂ` turns these absolute summability assumptions into
summability of the complex terms, so the displayed `tsum` values represent
the convergent sums.

## Rationale for a separate proof

The following explains why this internally derived statement is sound; the
steps remain proof obligations for its proof successor.

Fix `q`, `a`, `b`, and a bound `C` from the hypotheses. Choose a real
`σ > C` and put `r = exp (-σ * log q) > 0`, with `q` viewed as a
positive real number. Since `q > 1`, its real logarithm is positive.
For every real `t`, complex exponentiation of the positive base gives

```text
spectralPoint q (σ + i t) = r exp (-i t log q).
```

As `t` varies this parametrizes the whole circle of radius `r`. More
explicitly, for any real `θ` choose `t = -θ / log q`, obtaining
`spectralPoint q (σ + i t) = r exp (i θ)`. Matching this formula to
Mathlib's complex-power conventions is part of the future proof.

At the real parameter `s = σ`, absolute summability gives
`∑ₘ |aₘ| rᵐ < ∞` and `∑ₘ |bₘ| rᵐ < ∞`, with integer powers of the
positive radius. For every real `θ` and every integer `m`,

```text
|aₘ (r exp (i θ))ᵐ| = |aₘ| rᵐ.
```

Thus these summable constants dominate the two Fourier series uniformly
on the circle. Their sums
`Fₐ(θ) = ∑ₘ aₘ rᵐ exp (i m θ)` and
`Fᵦ(θ) = ∑ₘ bₘ rᵐ exp (i m θ)` agree everywhere by the half-plane
hypothesis. For each integer `n`, integrate against `exp (-i n θ)`
over a full period with normalized measure. Uniform absolute convergence
justifies interchanging the integer-indexed sum and the integral.
Orthogonality of the integer characters then yields

```text
(1 / (2π)) ∫₀²π Fₐ(θ) exp (-i n θ) dθ = aₙ rⁿ,
(1 / (2π)) ∫₀²π Fᵦ(θ) exp (-i n θ) dθ = bₙ rⁿ.
```

These extraction identities, their integrability hypotheses, and the
interchange are conclusions to prove, not premises of the Lean
statement. Equality of the functions gives `aₙ rⁿ = bₙ rⁿ`.
Since `rⁿ ≠ 0` for every integer `n`, cancellation in `ℂ` gives
`aₙ = bₙ`; extensionality gives `a = b`. A proof can establish a
separate one-circle uniqueness helper, or reuse an exact Fourier
uniqueness theorem after checking its sign, period, normalization, and
summability conventions.

## Intended later uses and algebraic boundary

A finite Laurent polynomial `Q` supplies the finitely supported
comparison series
`BilateralLaurentSeries.ofLaurentPolynomial Q`. A later application
will identify its finite evaluation with its bilateral sum, then apply
the proved uniqueness statement to an absolutely convergent series whose
spectral sum equals that evaluation. This will identify the original
coefficients and hence extract finite Laurent support.

For rational-denominator clearing, a later argument must first clear the
denominator in the analytic equality. It must also prove that the
spectral sum of the actual finite Laurent action `P • a` equals the
finite evaluation of `P` times the spectral sum of `a`, and verify
weighted absolute convergence of the resulting series. Finite
convolution and reindexing are the expected route. Only then can
uniqueness compare `P • a` with a finitely supported Laurent comparison
series. This module proves neither that compatibility nor any clearing,
support, rational-continuation, or adjacent-rank factor assertion.

The unrestricted bilateral module has torsion: the series with every
coefficient equal to `1` is annihilated by `1 - T 1`, as recorded by
`BilateralLaurentSeries.one_sub_T_one_smul_eq_zero`. Therefore a nonzero
Laurent polynomial cannot in general be cancelled from a formal module
identity. The proposed cancellation above is only of the nonzero complex
number `rⁿ`, after extracting one coefficient.

## Provenance and dependencies

The original source is H. Jacquet, I. I. Piatetski-Shapiro and J. A.
Shalika, *Rankin–Selberg Convolutions*, American Journal of Mathematics
105 (1983), 367–464; registered as `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The retained source is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
Printed pages 406–407 and 409–410 are one-based PDF pages 41–42 and
44–45, respectively, and were visually read for this statement.
No source-specific erratum was found in the project's public errata
locations.

Section (4.1), printed page 406, defines formal series with all integer
coefficients and their Laurent-polynomial module structure, explicitly
allowing torsion. Section (4.2), printed pages 406–407, associates
determinant-slice coefficients to convergent integrals and uses
`X = q^(-s)`. Those particular source series have only finitely many
nonvanishing negative terms. The present general scalar formulation
allows unrestricted bilateral support and uses absolute summability
instead; it is an internal analytic extraction, not a literal printed
JPSS theorem.

In the Section (4.5) argument on printed pages 409–410, analytic
dependence of the slice coefficients and polynomial clearing lead to
coefficient identities with a fixed finite range of shifts. This
motivates the intended later clearing application. The current statement
does not establish those representation-theoretic inputs or the
subsequent specialization in the deformation parameter.

The only imports are the published modules
`Langlands.HarmonicAnalysis.BilateralLaurentSeries` and
`Langlands.Representation.RankinSelberg.RationalContinuation`.
Existing Library Lean and Markdown files are unchanged. The designated
Lean environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
