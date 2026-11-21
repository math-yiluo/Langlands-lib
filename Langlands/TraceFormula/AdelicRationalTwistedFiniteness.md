# Finiteness of rational twisted classes on compact norm-one support

`adelicRationalTwistedFiniteness` proves `AdelicRationalTwistedFinitenessStatement`.
It takes `GeneralLinearWeilAdelicTwistStatement` as a premise.
For a cyclic extension of number fields `L/K`, take a compact set
in the norm-one group of `Res_{L/K} GL_n` whose cyclic norms are
regular elliptic at a fixed finite place of `L`. The proposition
gives a single finite list of rational norm-one representatives.
Every rational twisted class meeting the compact set contains one
of those representatives.

The proof transports the compact set into adelic matrix coordinates
and takes its image under the continuous cyclic norm. The Library's
ordinary elliptic finiteness theorem over `L` bounds the rational
conjugacy classes of the resulting norms. For each occurring norm
representative the proof chooses a rational upper matrix with that
norm. A rational conjugator of norm matrices gives a rational
twisted conjugator by `cyclicNormLemma`.

The coordinate comparison respects the arithmetic automorphism and
the rational embedding, so these representatives and conjugators
transport to the original norm-one group. The proof uses the
upper-place regular ellipticity condition of the Library's simple
twisted trace formula. Together with `positiveAverageOrbitSupport`,
it gives a common finite list for tests whose positive averages
are bounded by the compact set.

This is an internal reduction in the geometric comparison of the
simple trace formulas. The ellipticity and norm-one conventions
follow the Library's `GeneralLinearSimpleTwistedTraceFormulaStatement`,
based on Getz–Hahn, §18.5. The finite support refinement at the
auxiliary place in Henniart–Lemaire, I.6.8, printed pp. 49–50
(PDF pp. 57–58), motivates using a bound fixed before shrinking
the support.
