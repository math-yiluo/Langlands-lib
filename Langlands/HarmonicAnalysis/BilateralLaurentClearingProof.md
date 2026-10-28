# Proof of bilateral Laurent clearing from opposite support bounds

Author: Worker 792.

This module proves the published proposition
`Langlands.HarmonicAnalysis.BilateralLaurentClearingStatement` as the theorem

```lean
theorem Langlands.HarmonicAnalysis.bilateralLaurentClearing :
    BilateralLaurentClearingStatement
```

It imports only `Langlands.HarmonicAnalysis.BilateralLaurentClearingStatement`.
That statement pair and the `Langlands.HarmonicAnalysis.BilateralLaurentSeries`
module it imports are unchanged. The proof uses that module's coefficient type,
Laurent-polynomial action, finite-convolution formula `laurent_smul_apply`, the
two support predicates with their characterizations
`hasLowerBoundedSupport_iff` and `hasUpperBoundedSupport_iff`, the coefficient
embedding `ofLaurentPolynomial` and its injectivity
`ofLaurentPolynomial_injective`.

## What is proved

For every pair of bilateral series `a b : BilateralLaurentSeries` (arbitrary
coefficient functions `ℤ → ℂ`) and every pair of Laurent polynomials
`P Q : LaurentPolynomial ℂ`, if the support of `a` is bounded below, the
support of `b` is bounded above, and `P • a = Q • b`, then there is a unique
Laurent polynomial `R` with `ofLaurentPolynomial R = P • a` and
`ofLaurentPolynomial R = Q • b`. Here `•` is the published module action, and
`ofLaurentPolynomial R` is the series `n ↦ R.coeff n`.

The proof adds no hypothesis. `P` and `Q` may be zero or non-invertible; neither
`a` nor `b` is assumed to have finite support. No support bound on the products
and no existence of `R` is assumed: both are derived. The case `P = Q = 0` is
covered: then `P • a = 0`, and `R = 0`.

## Supporting lemmas

All four lemmas are in the namespace
`Langlands.HarmonicAnalysis.BilateralLaurentSeries`.

1. `HasLowerBoundedSupport.laurent_smul`: if `a` has support bounded below,
   then so does `P • a`, for every Laurent polynomial `P`. By
   `hasLowerBoundedSupport_iff` there is `N` with `a j = 0` for all `j < N`.
   The finite set `P.coeff.support` has a lower bound `m` (Mathlib's
   `Finset.bddBelow`; when `P = 0` the set is empty and any `m` works). For
   `n < N + m`, each term `P.coeff k * a (n - k)` of the finite sum given by
   `laurent_smul_apply` has `m ≤ k`, so `n - k < N` and the term vanishes.
   Hence `(P • a) n = 0` for all `n < N + m`.
2. `HasUpperBoundedSupport.laurent_smul`: the mirror statement. If `b j = 0`
   for all `N < j` and `M` bounds `P.coeff.support` above, then for
   `N + M < n` every index `k` of the sum has `k ≤ M`, so `N < n - k` and
   `(P • b) n = 0`.
3. `finite_support_of_hasLowerBoundedSupport_of_hasUpperBoundedSupport`: a
   series `c` whose support `{n : ℤ | c n ≠ 0}` is bounded below and above has
   finite support. This is Mathlib's `BddBelow.finite_of_bddAbove` for the
   locally finite order `ℤ`, applied directly to the two support predicates,
   which are by definition `BddBelow` and `BddAbove` of that set.
4. `exists_ofLaurentPolynomial_eq_of_hasLowerBoundedSupport_of_hasUpperBoundedSupport`:
   such a series `c` equals `ofLaurentPolynomial R` for some Laurent polynomial
   `R`. The witness is
   `AddMonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite (fun n : ℤ => c n) _)`,
   the Laurent polynomial whose coefficient function is exactly `c`, built from
   the finiteness in lemma 3. The equality is checked coefficientwise and holds
   by definition.

## Proof of the theorem

Let `a b P Q` satisfy the three hypotheses `ha`, `hb` and `hab : P • a = Q • b`.

- By lemma 1, `P • a` has support bounded below.
- By lemma 2, `Q • b` has support bounded above; rewriting with `hab`, so does
  `P • a`.
- By lemma 4, there is `R` with `ofLaurentPolynomial R = P • a`. Composing
  with `hab` gives `ofLaurentPolynomial R = Q • b`.
- Uniqueness: if `S` also satisfies `ofLaurentPolynomial S = P • a`, then
  `ofLaurentPolynomial S = ofLaurentPolynomial R`, and
  `ofLaurentPolynomial_injective` gives `S = R`. Only the first of the two
  equalities for `S` is used.

## Relation to the source

Source: H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg convolutions*, Amer. J. Math. 105 (1983), Section (4.4),
printed page 408, the paragraph following (4.4.1). Registered source
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`. No errata
are registered for this source.

The source observes that one side of (4.4.1) is a series bounded below, since
`Ψ(s, W, W'; Φ)` is and the other factors are polynomials in `X, X⁻¹`, and
that the other side is similarly bounded above, so both sides are polynomials
in `X, X⁻¹`. Lemmas 1 and 2 make precise the step "the other factors are
polynomials, so the product is again such a series". Lemmas 3 and 4 make
precise "both sides are a posteriori polynomials". Uniqueness of `R` is not
in the source; it is the derived strengthening recorded in the statement's
Markdown, and it follows from injectivity of the coefficient embedding.

## Scope

This is a scalar algebraic lemma about the published bilateral coefficient
module. It does not prove the formal identity (4.4.1) or any instance of
`P • a = Q • b` for JPSS integrals, and it does not show that any JPSS integral
has a one-sided support bound. It does not show that `a` or `b` is a Laurent
polynomial, and it does not cancel `P` or `Q`. It makes no claim about analytic
continuation, determinant-slice support, the existence of gamma or `L`-factors,
or multiplicativity.
