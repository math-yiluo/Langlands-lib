# Unequal pointwise factorization from ordinary archimedean tests

`UnequalPointwiseFactorizationFromGlobalReflectionStatement` implies the
exact `UnequalPointwiseFactorizationStatement.{u,uQ}` from
`RealUnequalOrdinaryPlaceTestsStatement.{u}` and
`ComplexUnequalOrdinaryPlaceTestsPositiveRankStatement.{u}`. The latter
covers smaller group rank at least two. The field and spectral presentation
universes stay independent.

Choose actual real and complex restrictions with nonzero ordinary integrals
arbitrarily far to the right. At real places the uniform Whittaker models give
regularity and holomorphy in a convergence half-plane. At complex places
`complexUnequalOrdinaryPlaceTests_of_positiveRank` supplies the smaller
\(\mathrm{GL}_1\) case. The ordinary part of the complex place equation gives
the required holomorphy for the complex tests. At each place in \(S\), use a
finite test with the previously proved ordinary and dual nonvanishing. On a
right half-plane its ordinary value is a rational function of \(q_v^{-s}\)
whose denominator is nonzero there. It is therefore holomorphic there.

The infinite Whittaker slice comparison realizes the chosen restrictions
simultaneously on each of the two infinite tensors, up to nonzero scalars.
Joining the infinite tensors to the finite test vectors gives vectors
spherical outside \(S\). The pointwise kernel lemmas give the ordinary product
and the dual product with the rectangular support indicator. The common scale
is the product of the two Whittaker normalization scalars.

Integrating the ordinary identity with `unipotentClassProductStatement` gives
a nonzero constant times the product of the ordinary tests. Since the product
is holomorphic on a common right half-plane and is nonzero there, it has a
nonzero value on every right half-plane. The global reflection argument gives
the same conclusion for the partial dual integral with these vectors. For its
product formula, the proof first integrates the rectangular indicator and
local factors by `rectangleTateStatement`, and then applies the quotient
product formula to the resulting functions. Nonvanishing of the partial dual
integral therefore implies nonvanishing of the archimedean dual product at the
same spectral value.

The factorization concerns the pointwise step of Cogdell, *Analytic Theory of
L-Functions for GLₙ*, proof of Theorem 4.1, printed pp. 219–220
(`cogdell-2004-analytic-theory-gln`). The implemented argument derives dual
nonvanishing by the global functional equation for the cuspidal integrals
from Theorem 2.1, printed p. 207. Jacquet's *Archimedean Rankin–Selberg
integrals*, (2.4)–(2.5) and Theorem 2.1, author p. 6
(`jacquet-2009-archimedean-rankin-selberg`), gives the form of the local
ordinary and dual integrals.
