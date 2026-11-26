# Gamma orders under sufficiently ramified twists of cuspidal pairs

`CuspidalPairRamifiedGammaOrderStatement` gives a conductor threshold for the local factor of the first-member twist of a cuspidal pair. For conductor at least that threshold, the local gamma function has order zero at every complex spectral point. It uses the local factors from `AutomorphicTwistSetup` on genuine cuspidal presentations.

For each of the ordinary and contragredient pairs, the comparison of generic Langlands quotients with their standard modules identifies the chosen polynomial with the integral Rankin–Selberg polynomial. Finite-place genericity supplies Whittaker type. The local highly ramified L-vanishing theorem then makes both polynomials equal to one. Inversion of the character preserves conductor, so the maximum of the two thresholds suffices. The gamma function is the remaining epsilon monomial. The spectral point is nonzero and the epsilon coefficient is a unit, so this monomial is analytic and nonzero and has order zero.

This is the local vanishing step in Henniart–Herb (1995), §8.16, printed p. 183 after (16), using the Rankin–Selberg vanishing theorem of Jacquet–Piatetski-Shapiro–Shalika (1983), Proposition 2.13, printed p. 404.

The retained Henniart–Herb source `henniart-herb-1995-induction` has SHA-256 `5e753525048b08007d9605baa9019c8e792512887305ec2e39ae9c3bee6a963e`. The retained Rankin–Selberg source `jpss-1983-rankin-selberg` has SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
