# Clearing bilateral Laurent series from opposite support bounds

Author: Worker 792.

This module states the proposition
`Langlands.HarmonicAnalysis.BilateralLaurentClearingStatement`. It supplies
no proof. The declaration is a transparent `def` returning `Prop`. It imports
only `Langlands.HarmonicAnalysis.BilateralLaurentSeries` and uses that
module's coefficient type, Laurent-polynomial action, support predicates and
coefficient embedding without change.

## The proposition

The statement quantifies over two bilateral series
`a b : Langlands.HarmonicAnalysis.BilateralLaurentSeries` and two Laurent
polynomials `P Q : LaurentPolynomial ℂ`. A bilateral series is an
unrestricted coefficient function `ℤ → ℂ`. Its variable is Mathlib's `T 1`,
which plays the role of the source's `X`. The hypotheses are:

1. `BilateralLaurentSeries.HasLowerBoundedSupport a`: the set
   `{n : ℤ | a n ≠ 0}` is bounded below. By the published
   `hasLowerBoundedSupport_iff`, this means there is `N` with `a n = 0` for
   every `n < N`.
2. `BilateralLaurentSeries.HasUpperBoundedSupport b`: the set
   `{n : ℤ | b n ≠ 0}` is bounded above. By the published
   `hasUpperBoundedSupport_iff`, this means there is `N` with `b n = 0` for
   every `N < n`.
3. `P • a = Q • b`. Here `•` is the published module action of
   `LaurentPolynomial ℂ` on bilateral series, the finite convolution
   `(P • a) n = ∑ k ∈ P.coeff.support, P.coeff k * a (n - k)` of the
   published `laurent_smul_apply`.

The conclusion is

```text
∃! R : LaurentPolynomial ℂ,
  BilateralLaurentSeries.ofLaurentPolynomial R = P • a ∧
  BilateralLaurentSeries.ofLaurentPolynomial R = Q • b.
```

Here `ofLaurentPolynomial R` is the bilateral series `n ↦ R.coeff n`. The
conclusion says that the common series `P • a = Q • b` is the coefficient
series of a Laurent polynomial `R`, and that `R` is unique. Both equalities
are kept in the conclusion, although each follows from the other and the
third hypothesis.

No further hypothesis is imposed. `P` and `Q` are arbitrary and may be zero
or non-invertible. Neither `a` nor `b` is assumed to have finite support. There
is no convergence, coefficient bound or rational-function hypothesis. The
equality `P • a = Q • b` is an assumption of this lemma.

The proposition concerns only the common multiple. It does not say that `a`
or `b` is a Laurent polynomial. For example, when `P = Q = 0` the hypotheses
hold for every series `a` with support bounded below and every series `b`
with support bounded above.

## Source and derived provenance

Source: H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg convolutions*, Amer. J. Math. 105 (1983), Section (4.4),
printed page 408, the paragraph following identity (4.4.1). Registered
source `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`. Printed
page 408 is one-based PDF page 43 (zero-based index 42) of the scan. No
errata are registered for this source.

The source interprets (4.4.1) as an equality of formal Laurent series in
`X = q^{-s}`. On its right side, `Ψ(s, W, W'; Φ)` is multiplied by
`ω_σ(-1)^{r-1}`, two epsilon factors and two inverse `L`-factors. On its left
side, `Ψ(1 - s, W̃, W̃'; Φ̂)` is multiplied by two inverse `L`-factors at
`1 - s`. The source argues as follows. `Ψ(s, W, W'; Φ)` has the form
`∑ aₙ Xⁿ` with `aₙ = 0` for `n ≪ 0`. The other factors on the right are
polynomials in `X, X⁻¹`, so the right side is again such a series.
Similarly, the left side is a series `∑ aₙ Xⁿ` with `aₙ = 0` for `n ≫ 0`.
Hence, once (4.4.1) is established, both sides are polynomials in
`X, X⁻¹`.

This proposition abstracts only that algebraic deduction:

- `a` corresponds to the series `Ψ(s, W, W'; Φ)`, whose support is bounded
  below. This is `HasLowerBoundedSupport a`.
- `b` corresponds to the series in `X` attached to `Ψ(1 - s, W̃, W̃'; Φ̂)`.
  Its expansion in `q^{-(1-s)}` has only finitely many negative terms. Since
  `q^{-m(1-s)} = q^{-m} X^{-m}`, the series in `X` has support bounded above.
  We read this as the reasoning behind the source's "Similarly". It
  corresponds to `HasUpperBoundedSupport b`.
- `P` and `Q` correspond to the products of the remaining factors on the
  right and left sides, which the source calls polynomials in `X, X⁻¹`.
  Here they are arbitrary elements of `LaurentPolynomial ℂ`.
- The formal identity (4.4.1) corresponds to the hypothesis `P • a = Q • b`.
  The source says that the right side of (4.4.1) is bounded below and the
  left side bounded above. Here the bounds are hypotheses on the series `a`
  and `b` before multiplication. That a Laurent-polynomial multiple keeps a
  one-sided bound is left to the proof.
- The source's conclusion "both sides are a posteriori polynomials in
  `(X, X⁻¹)`" is the existence of `R` with
  `ofLaurentPolynomial R = P • a` and `ofLaurentPolynomial R = Q • b`.

The uniqueness of `R` is not in the source. It is a derived strengthening,
which holds because the published coefficient embedding
`ofLaurentPolynomial` is injective (`ofLaurentPolynomial_injective`).

The proposition is a scalar algebraic lemma. Nothing in it refers to
representations, Whittaker functions, Schwartz functions or integrals. The
correspondence above explains its intended use and is not formalized here.

## Scope

This module makes no analytic claim and proves nothing. It does not prove the
formal identity (4.4.1) or any instance of `P • a = Q • b` for JPSS
integrals. It does not show that any JPSS integral has a one-sided support
bound. It does not state that epsilon or `L`-factors are Laurent
polynomials. It supplies no Whittaker coefficient bound, dual or reflection
identity, determinant slice expansion, rational continuation, functional
equation, existence of gamma or `L`-factors, or multiplicativity.
The published `BilateralLaurentSeries` module and its imports are unchanged.
