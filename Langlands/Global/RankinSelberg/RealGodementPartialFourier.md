# Rapid decay of the partial real Fourier integral

The positive Fourier integral in the first factor of a real product Schwartz test uses the self-dual measure for the specified character. It is jointly continuous in the frequency and the untouched coordinate. Its absolute value times `(1 + ‖frequency‖)^N (1 + ‖coordinate‖)^N` is bounded for every nonnegative integer `N`.

Schwartz seminorms give an integrable majorant for each affine slice, including after inserting a power of the norm of the fixed coordinate. Dominated convergence gives continuity. The original integral gives arbitrary decay in the untouched coordinate. The complementary-slice formula expresses the same integral through the full real Schwartz Fourier transform and gives arbitrary decay in the frequency. Comparing the two weights and using order `2N` in the larger coordinate gives the simultaneous estimate. `scaledFirstFactorFourier_decay_seminorm` bounds this estimate for every test by one continuous real seminorm, obtained by adding the original slice seminorm and the complementary seminorm composed with the full scaled Fourier map.

This estimate is the partial Fourier input used in the proof of Proposition 7.2 in Hervé Jacquet, *Archimedean Rankin–Selberg Integrals*, Section 7.2. The proof establishes the value estimates needed there for an arbitrary real product decomposition.
