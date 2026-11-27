# The transverse Fourier trace of a smooth real Whittaker functional

`RealParabolicTransverseTraceStatement` fixes two rank-matched standard Levi vectors and a continuous Whittaker functional on the smooth standard module of their concatenation. Its evaluation on the genuine smooth compact parabolic section is a scalar multiple of the transverse Fourier moment. The scalar may depend on the two vector inputs and the Whittaker functional. The moment uses the self-dual rectangular measure and the negative character on the entry in the last row and first column.

The section map is continuous and complex linear in the compact rectangle test, so composition with the Whittaker functional is a distribution. The right rectangle translation shifts the test by the same rectangle. The superdiagonal sum of that unipotent matrix is its boundary entry, so the distribution transforms by the positive boundary character. `TranslationCovariantDistribution` identifies it with a scalar multiple of the negative-character integral. A compact test of moment one is obtained by multiplying a smooth bump by the positive character and dividing by the positive integral of the bump.

This proves the transverse Fourier dependence of the compact sections in Jacquet, *Archimedean Rankin–Selberg Integrals*, proof of Proposition 14.1, pp. 103–104 of the author-posted edition. The proportionality statement concerns the rectangle test for fixed Levi inputs.

`contDiff_transversePhase` and `transversePhase_zero` give smoothness of the
phase and its value at the zero rectangle. The restriction of the full
Whittaker character to the exchanged upper rectangle is
`whittakerCharacter_intertwiningUnipotent`.
