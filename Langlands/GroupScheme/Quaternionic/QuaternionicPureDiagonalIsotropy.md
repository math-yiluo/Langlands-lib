# Scalar equation for local skew isotropy on a pure diagonal

`HasNonzeroSkewNormZero a c d` means that a tuple of four scalar coordinates per row entry, with at least one coordinate nonzero, satisfies the sum of the weighted norm equations `∑ᵢ aᵢ(u₀ᵢ² - c u₁ᵢ² + d(v₀ᵢ² - c v₁ᵢ²)) = 0`. The proposition is preserved by injective scalar maps.

For a scalar extension to a field `R`, a nonzero isotropic row of the diagonal skew form with entries `aᵢ ⊗ x` gives this equation for the images of the quaternion parameters `c = x²` and `d = j²`. Write both quadratic-field coordinates of each row entry in the basis `1, root`, then project the zero skew value onto the first quaternionic coordinate. The pure root factor is a unit. Cancelling it and using the injectivity of the scalar map gives the displayed equation. If all the scalar coordinates vanish, the original row vanishes.

The equation is the coefficient consequence of the local skew isotropy used in Springer's appendix to Kneser, *Lectures on Galois Cohomology of Classical Groups* (1969), Theorem 5.3.3(i), printed p. 110 (PDF p. 116).
