# Boundary asymptotics of a continuous logarithm

Lean module `Langlands.Analysis.LogarithmicAsymptotics`.
`BoundaryLogarithmAsymptoticsStatement` is proved by
`tendsto_div_log_of_meromorphicOrderAt`.

Fix a real `θ` and suppose `f : ℂ → ℂ` is meromorphic of finite integer
order `n` at `z₀ = 1 + iθ`. Let `l` be continuous on the real interval `(1,a)`
for some `a > 1` and satisfy `exp(l(σ)) = f(σ + iθ)` there. The conclusion is

\[
\lim_{\sigma\to1^+} \frac{l(\sigma)}{\log(1/(\sigma-1))}=-n.
\]

This gives 1 at a simple pole and 0 at a nonzero regular germ. It also covers
zeros through positive order. The order and the limit use the punctured
neighbourhood of `z₀`.

## Proof

By `meromorphicOrderAt_eq_int_iff`, the germ factors as
`f(z) = (z − z₀)^n g(z)`, with `g` analytic and nonzero at `z₀`. On a
sufficiently short interval to the right of 1, the values
`q(σ) = g(σ + iθ)/g(z₀)` lie within distance 1 of 1. The principal logarithm
of `q` is continuous there. Subtract `n log(σ−1)` and `log(q(σ))` from
`l(σ)`. The exponential of this corrected logarithm is constantly `g(z₀)`.
Its difference from a fixed logarithm of `g(z₀)`, divided by `2πi`, is a
continuous integer-valued function on an interval, so it is constant.
Therefore `l(σ)` equals `n log(σ−1)` plus a term with a finite limit.
Dividing by the positive quantity `−log(σ−1)`, which diverges to infinity,
gives the limit.

## Source

H. Jacquet and J. A. Shalika, *On Euler Products and the Classification of
Automorphic Forms II*, American Journal of Mathematics **103** (1981),
777–815. The proof of Theorem 4.1 compares continuous logarithms at a
nonzero regular point in displays (4)–(5), printed pp. 805–806 (one-based PDF
pp. 30–31). It treats the simple pole in displays (6)–(7), printed p. 806
(PDF p. 31). The Lean lemma combines these two arguments using the
meromorphic order factorization. Registered source
`jacquet-shalika-1981-euler-ii`, SHA-256
`4d3f68841a558631a1624482d497665c2b52059bb9e0b7333948b8d1610b57d8`.
