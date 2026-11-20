# Left vertical lines from the completed pair functional equation

`HasLeftVerticalLineBounds` says that to the left of every real abscissa there is a vertical line on which the function has bounded norm. `hasLeftVerticalLineBounds_of_completedEquation` proves this property for a continuation with the two-point simple-pole profile when a certified finite factor choice satisfies the completed functional equation with the specified archimedean factors.

The finite factor comparison identifies the two initial Euler products even when the factor data for the equation and for the continuation use different additive characters or measures. The meromorphic identity principle extends equality of the two continuations from their initial half-plane to equality on the codiscrete filter. On a sufficiently far-left line the given continuation is holomorphic, and the dual function is continuous at the reflected points by its agreement with the initial completed Euler product on a sufficiently far-right half-plane. Continuity then extends the functional equation to every point on the chosen line.

Each finite epsilon factor is a constant times an integral power of the local spectral point, so its modulus depends only on the real part. The same property follows for the real and complex epsilon factors from their explicit Gamma-block formulas with positive bases. The modulus of their product is therefore constant on the left line. The right-strip bound for the dual completion on the reflected line gives the bound on the left line.

The reduction uses the completed equation in Getz–Hahn 2024, Theorem 11.7.1, printed p. 309, and the factor and measure conventions in the Library's `CompletedEquationHolds`. The completed equation itself is a hypothesis.
