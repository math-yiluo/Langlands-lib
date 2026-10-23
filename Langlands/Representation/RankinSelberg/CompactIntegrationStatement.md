# Finite compact averages of equal-rank integrands

`Langlands.RankinSelberg.EqualRankCompactIntegrationStatement F n` states a
finite weighted formula for the compact variable in the equal-rank JPSS
integrand. It uses the actual `equalRankFunction`, including its determinant
weight. The matrix rank is `n+1`, including rank one.

Let `K` be any compact subset of the general linear group and let `κ` be any
finite measure on its subtype, with the measurable structure inherited from
the ambient Borel structure. Let `abv` be an absolute value such that
`abv(det k)=1` for every `k` in `K`. For smooth representations `π, σ`, their
specified standard and inverse-character functionals, coefficient-model
vectors `f, f'`, and a Schwartz–Bruhat row test `Φ`, the proposition asserts
that there are finitely many representatives `k_i` in `K` and nonnegative
real weights `c_i` such that

\[
\sum_i c_i=\kappa(K).
\]

Here `κ(K)` means the mass of the entire subtype, represented in Lean by
`κ.real Set.univ`. The representatives and weights are chosen before the
arbitrary matrix `g` and complex spectral parameter `s`. For every such `g,s`,
write

\[
H_{g,s}(k)=f(gk)f'(gk)\Phi(e_{n+1}gk)|\det(gk)|^s.
\]

Then `H` is integrable over `κ`, and the actual integrals satisfy

\[
\int_K H_{g,s}(k)\,d\kappa(k)
 =\sum_i c_iH_{g,s}(k_i),\qquad
\int_K |H_{g,s}(k)|\,d\kappa(k)
 =\sum_i c_i|H_{g,s}(k_i)|.
\]

The absolute-value formula is stated using the nonnegative extended integral
and the extended norm. It therefore retains the identity needed to analyze
absolute convergence when another integration variable is introduced. The
weights are finite; for a probability measure they sum to one. Empty `K` is
allowed, with an empty family and zero mass. Neither a subgroup structure on
`K` nor invariance of `κ` is assumed.

The field has a topology making its ring operations continuous. The
representation universes are independent. Zero functionals and reducible
representations are allowed. No admissibility or finite-generation assumption
is needed for this compact averaging step. The determinant hypothesis is
explicit and concerns only `K`; it ensures that the spectral weight is
constant in the compact variable for fixed `g,s`. It does not impose a
condition on `g` or on the real part of `s`.

This is a derived interface for the compact-group reduction in
Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg Convolutions* (1983), proof of
Theorem 2.7, printed p. 391, paragraph preceding display (3) and display (3).
The source combines Iwasawa integration with finiteness of the simultaneous
compact translates. This proposition isolates the latter step at the level
of actual integrals. The published `EqualRankCompactDataStatement` and its
proof give a locally constant tuple consisting of the two translated model
vectors and the translated row function. On `K` its range is finite. Its
measurable fibers partition `K`; take their measures as the weights and
choose one representative in each nonempty fiber. The last row of `gk` is
the last row of `g` multiplied by `k`, so equality of these tuples fixes the
coefficient and row factors. The determinant hypothesis fixes the remaining
factor. Finite simple-function integration then gives both displayed
formulas and integrability.

This file defines a proposition, without proving it. It does not assert a
quotient Iwasawa measure identity, convergence in the noncompact torus
variable, rational continuation, a common denominator, or a normalized
generator. Applying it to the normalized compact subgroup also requires
identifying the finite measure on that subtype and verifying its determinant
norm condition.

Source: `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`,
printed p. 391, proof of Theorem 2.7, paragraph before (3) and display (3).
