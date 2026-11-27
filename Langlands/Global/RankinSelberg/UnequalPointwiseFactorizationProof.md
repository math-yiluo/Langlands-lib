# Pointwise factorization of unequal-rank Rankin–Selberg integrands

`Langlands.Global.RankinSelbergGlobal.unequalPointwiseFactorization` proves
`UnequalPointwiseFactorizationStatement.{u,uQ}`, with independent universes
for the number field and the spectral presentations.

The proof applies `unequalPointwiseFactorizationFromGlobalReflection` to
`realUnequalOrdinaryPlaceTests` and `complexUnequalOrdinaryPlaceTests`. It
restricts the complex theorem to smaller groups \(\mathrm{GL}_{t+1}\) with
\(t>0\), as the reduction supplies the complex \(\mathrm{GL}_1\) case
separately. The chosen local restrictions and measures are fixed as the
spectral variable varies.

The reduction realizes the chosen Whittaker factors on a pair of cuspidal
tensors, spherical outside the given set \(S\). The ordinary and dual pointwise
identities have the common scalar from the two Whittaker normalizations. The
dual identity also includes the indicator of rectangular integrality outside
\(S\). The ordinary quotient product and the unramified Euler factors give
a nonzero value of the entire global cuspidal integral. The global
functional equation and unfolding then give nonzero full dual values
arbitrarily far to the right for the same vectors. The unramified cell
calculation transfers this nonvanishing to the partial dual integral.
Integrating the dual pointwise identity over the rectangular variables and
the integral unipotent classes gives archimedean dual nonvanishing.

The statement formalizes the pointwise step in the proof of Theorem 4.1
of J. W. Cogdell, *Analytic Theory of L-Functions for GLₙ*,
printed pp. 219–220 (`cogdell-2004-analytic-theory-gln`). The global reflection
uses the analytic and functional-equation clauses of Theorem 2.1,
printed p. 207.
