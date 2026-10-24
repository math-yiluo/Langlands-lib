# Proof of the conditional compact-root analytic bridge

`Langlands.RankinSelberg.equalRankRootAverageAnalytic` proves
`EqualRankRootAverageAnalyticStatement` for independent field and representation
universes. The full finite-function Mellin proposition remains an explicit
premise. The proof uses the actual normalized torus and restricted compact
measures specified by the target.

First, `equalRankCompactRootExpansion` chooses the finite family `η` before
any functional or test data. The proof forms its finite image `X` and applies
the Mellin premise with positive weights `i.val + 1`. Its common nonzero
Laurent denominator `D` is therefore fixed before the Whittaker functionals,
coefficient vectors and row test. The auxiliary set `values` consists of all
rational continuations of Mellin integrals with a function in `X` and an
arbitrary full-coordinate Schwartz test.

For fixed functionals and test data, the compact expansion provides the
finite coefficients `c` and Schwartz functions `Ψ`. Write `I(t,j,s,a)` for
the corresponding Mellin integrand and `S(t,s,a) = ∑ j, I(t,j,s,a)`. The
expansion gives the exact compact-average identity
`B(s,a) = ∑ t, (c_t : ℂ) * S(t,s,a)` and the exact absolute-average identity
`∫⁻ z, ‖H(s,a,z)‖ₑ = ∑ t, ENNReal.ofReal(c_t) * ‖S(t,s,a)‖ₑ`.

The Mellin convergence clause supplies a bound for each pair `(t,j)`.
Boundedness of the finite range of these real bounds gives a single upper
bound, also handling an empty index set. On the resulting right half-plane,
finite-sum integrability gives integrability of every `S_t` and then of `B`.
For the absolute integral, the exact compact formula is substituted first.
Almost-everywhere measurability of the extended norms follows from
integrability of the `S_t`. `lintegral_finsetSum'` and
`lintegral_const_mul'` give a finite sum of finite nonnegative terms, since
`ENNReal.ofReal(c_t)` is finite and each `S_t` has finite integral of its
extended norm. The norm of an inner sum is retained throughout.

The same convergence bound justifies both finite Bochner-integral sum
interchanges, identifying the actual iterated integral with
`∑ t, (c_t : ℂ) * ∑ j, ∫ I(t,j,s,a) dA(a)` on that half-plane. The Mellin
rationality clause supplies `R(t,j)` for each summand. The helpers
`continuation_sum` and `continuation_linear_combination` give the rational
function `∑ t, RatFunc.C(c_t) * ∑ j, R(t,j)`, and
`continuation_of_eq_on_right` transfers this continuation to the actual
iterated integral.

Each `R(t,j)` belongs to `values`. Closure of its Laurent span under finite
sums and scalar multiplication places the constructed continuation in
`zetaSpan values`. Complex constants act through the actual constant Laurent
polynomials; `algebraMap_laurent` and `laurentToRatFunc_C` identify the scalar
action. `denominator_clears_span` consequently clears the constructed
continuation with the original `D`. Finally, for any continuation given in
the target, `HasRationalContinuation.unique` and
`T.residueCardinality_gt_one` identify it with the constructed one. This
proves the fixed-denominator clause for every continuation, uniformly over
all functionals and test data.

The argument is an internal assembly of the imported interfaces and
Mathlib integration facts. It does not prove the Mellin premise, product
measurability, quotient transport, or normalized-generator existence.
