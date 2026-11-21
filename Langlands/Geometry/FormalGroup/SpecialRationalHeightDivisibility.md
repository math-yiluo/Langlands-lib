# Signed height divisibility on special atlases

For the actual central tensor quasi-isogeny of two special formal modules of scalar height \(d^2\), this module proves that its signed \(q\)-normalized height at each base prime is divisible by the division degree \(d\).

`fieldHeightPresentation` clears the denominator of the actual tensor over a field. The field kernel-rank theorem supplies the numerator exponent in base \(q\). `fieldHeightNumerator` verifies that this integral numerator commutes with the full division order by injectivity of rationalization for a divisible source. Over a geometric residue field, the integral-height divisibility theorem applies to the numerator. The scalar denominator has height a multiple of \(d^2\), so the signed difference is a multiple of \(d\).

`SpecialModule.dvd_heightFunction` reads the height at a prime by pulling back the quasi-isogeny to the algebraic closure of that prime's residue field. The nilpotent structural uniformizer maps to zero there. The coefficient algebra therefore factors through the central residue field. Naturality of the measured height identifies the field result with the original signed height at the prime.

`SpecialAtlas.dvd_heightFunction` chooses a chart containing the prime and a prime of its actual localization over it. Every chart test reads the pullback of the base height, so the divisibility holds for the locally constant height of the whole atlas.

This argument is derived from Drinfeld, *Coverings of p-adic symmetric regions* (1976), §2A, printed p. 109 (PDF p. 3), and supplies the division-degree normalization for the first split component coordinate of Harris (1997), Appendix (A.3), printed p. 114 (PDF p. 40).
