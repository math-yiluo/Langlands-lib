# Proof of finite compact averages

`Langlands.RankinSelberg.equalRankCompactIntegration` proves
`EqualRankCompactIntegrationStatement F n` with independent field and
representation universes. It retains the statement's arbitrary compact subset,
arbitrary finite subtype measure, smooth coefficient-model data, Schwartz row
test, and explicit determinant norm-one condition.

The private helper `CompactIntegration.finite_average` works with any locally
constant finite-range map `D : A → B` on a space whose open sets are measurable,
and any finite measure `μ` on `A`. It enumerates the range of `D` by `Fin m`.
The resulting label map is measurable because its fibers are the open fibers
of `D`. Choose one representative `k_i` in each fiber, push `μ` forward along
the label map to a finite measure `ν`, and set `c_i = ν.real {i}`. The weights
are nonnegative and their sum is `μ.real Set.univ`, by finite additivity on
singletons and the pushforward formula.

Every complex-valued function `H` constant on the fibers factors through the
finite label set as `h(i) = H(k_i)`. The finite-space function `h` is integrable
for `ν`; the measurable pushforward identity transfers integrability to `H`.
The Bochner integral pushforward identity and `integral_fintype` give

\[
\int_A H\,d\mu=\sum_i c_iH(k_i).
\]

The nonnegative integral pushforward identity and `lintegral_fintype` likewise
give

\[
\int_A \lVert H\rVert_e\,d\mu
  =\sum_i \operatorname{ofReal}(c_i)\lVert H(k_i)\rVert_e.
\]

Finiteness of `ν` identifies `ofReal (ν.real {i})` with `ν {i}`. The construction
also works when the domain is empty: its range and label set are empty.

For the equal-rank specialization, apply `equalRankCompactData` to the tuple
of the two translated coefficient-model vectors and the entire translated
row-test function. Restrict this tuple to the subtype of the compact set `K`.
Continuity of the subtype inclusion preserves local constancy, and the
compact-data theorem supplies finite range.

Equality of two tuple values implies equality of both translated coefficients
after evaluation at any `g`. Evaluating equality of the row-test functions at
`lastRow g` gives equality of the row factors, because the last row of `gk` is
the last row of `g` multiplied by `k`. These evaluation identities are
definitional for the Library's model action and matrix multiplication.
Multiplicativity of the determinant and the absolute value, together with
`abv(det k)=1` on `K`, gives
`determinantWeight abv (g*k) s = determinantWeight abv g s`.
Thus the actual `equalRankFunction` is constant on every tuple fiber for every
`g,s`. The helper chooses its representatives and weights before `H`, so one
family works for all `g,s`, for both integrals and for integrability.

This is the finite measurable-fiber proof of the derived compact reduction
described in `CompactIntegrationStatement.md`, whose source is the compact
finiteness step preceding display (3) in Jacquet–Piatetski-Shapiro–Shalika,
*Rankin–Selberg Convolutions* (1983), printed p. 391. The implementation uses
the published compact-data theorem and elementary finite-space integration.
It does not prove quotient Iwasawa integration, convergence in the noncompact
variables, rational continuation, a common denominator, or a normalized
generator. Those remain separate obligations for the full analytic theorem.
