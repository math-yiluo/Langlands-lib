# Eisenstein continuation from the induced equations and cuspidal tests

`Langlands.Global.eisensteinMeromorphicContinuation_of_induced_of_cuspidalTests`
proves `EisensteinMeromorphicContinuationStatement` given
`InducedHarishChandraEquationsStatement` and `EisensteinCuspidalTestSystemStatement`.
The first supplies the convolution equations on the twisted inducing section.
`eisensteinHarishChandraEquations_of_induced` transports them through the sum
defining the Eisenstein series in the convergence region.

`eisensteinSystemDomination_of` uses these equations and the cuspidal tests,
together with `eisensteinCommonGrowth`, `parabolicCuspidalVanishing`,
`localFinitenessSolutionAutomorphy` and `positiveTorusSplitComponent`, to
dominate the characterizing system by a local-finiteness system. The
characterizing system has the convergent series as its unique solution at
sufficiently positive parameters. The reduction
`eisensteinAnalyticSystem_of_localFiniteness_of_domination` applies
`uniformGrowthLocalFiniteness` to the dominating system and obtains local
finite-dimensional bounds for the characterizing system.

`eisensteinMeromorphicContinuation_of_analyticSystem` applies
`meromorphicContinuationHolomorphic` to obtain meromorphic solution
families in the uniform-growth Fréchet spaces. It glues their underlying
functions by meromorphic uniqueness on charts containing a common open set
of regular parameters. At parameters in a chart's unique-solution locus,
the resulting functions are automorphic by the solution property of the
analytic system.

The composition follows J. Bernstein and E. Lapid,
*On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc.
37 (2024), §8.3 and §8.4, equations (8.2a–b) and the proposition and proof
on pp. 223–224 (PDF pp. 37–38). The continuation principle is Theorem 3.3,
p. 194 (PDF p. 8), and the Fréchet-space formulation is the corollary at
the end of §8.6, p. 226 (PDF p. 40). The registered journal PDF is
`bernstein-lapid-2024-meromorphic-continuation-eisenstein-published`, SHA-256
`6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`.
