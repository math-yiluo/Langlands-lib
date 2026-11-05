# Polynomial isolation of a distinguished submodule

This is internal algebra supporting the finite-length standard-intertwining
route. It works over any commutative ring `R` and any `R`-module `V`, with
independent ring and carrier universes. It constructs no actual Jacquet
filtration, exponent annihilators, analytic continuation or nonvanishing
denominator, and proves no whole intertwining theorem.

For a linear endomorphism `T`, write `f(T)` for `Polynomial.aeval T f`.
The theorem `aeval_prod_range_mem` takes a finite list of polynomials `p i`
and submodules `F i`. Its hypothesis is that `p i(T)` sends every vector of
`F (i+1)` into `F i`, for every index below the chosen length `n`.
It concludes that the product of all these polynomials sends `F n` into
`F 0`. No monotonicity or invariance of the submodules is assumed.
The proof inducts on the length, applies the last factor first, and then
uses the induction hypothesis on the remaining factors.
`aeval_prod_range_eq_zero` gives annihilation when `F 0` is bottom.
The empty product and length zero are included.

The construction `polynomialRangeMap T U q b hq` is the actual `R`-linear
map from `V` into `U` obtained by restricting the codomain of `(q*b)(T)`.
Its assumption `hq` states that `q(T)` sends every vector of `V` into `U`.
Multiplicativity of evaluation proves membership by applying `b(T)` first
and `q(T)` second. `polynomialRangeMap_apply` exposes the ambient formula.

Suppose also that `p(T)` kills every vector of `U`, and polynomials `a`, `b`
and a scalar `c` satisfy `p*a + q*b = C c`.
The theorem `polynomialRangeMap_eq_smul` proves that this map takes every
`u : U` to `c • u`. To prove it, commute `p` and `a` before evaluation, so
that `p(T)` acts on `u` first; its contribution is zero. Evaluating the
Bezout identity leaves exactly `(q*b)(T) u = c • u`.
Thus the assertion requires no stability of `U` under `T`.
The scalar and the polynomial multiplier are fixed before all vectors.

`exists_resultant_polynomialRangeMap` uses Mathlib's
`Polynomial.exists_mul_add_mul_eq_C_resultant` to produce the multiplier
`b` with `c = p.resultant q m n`. Its degree bounds are
`p.natDegree ≤ m` and `q.natDegree ≤ n`, and it retains the necessary
condition `m ≠ 0 ∨ n ≠ 0`. Both degree bounds zero are excluded because
the degree-zero resultant is one even when the two constant polynomials
do not generate the unit ideal. The result does not assume or conclude
that the resultant is nonzero or a unit.

The provenance is derived polynomial and module algebra: polynomial
evaluation is multiplicative, polynomials over a commutative coefficient
ring commute, linear maps can be restricted to a proved target submodule,
and Mathlib supplies the resultant Bezout identity over that same ring.
No external representation-theoretic assertion is used or transcribed.

Author: Worker 1615.
