# Entire continuation of normalized product Tate integrals

For a Schwartz test on a finite product of complex planes and integer angular weights, multiply the additive product Tate integral by the reciprocal factors `Gammaℂ (u j + |m j| / 2)`. If `u j = t j + c j * s` with complex offsets and real slopes, the normalized integral extends to an entire function of `s`. The extension agrees with the normalized integral wherever all parameter real parts are positive.

Lean constructs extensions by induction on a set of coordinates in which the real-part restrictions have been removed. Initially the holomorphy of the convergent integral and of the reciprocal Gamma factors give the extension. For a new coordinate, use the original expression on the positive half-plane and the coordinate Fourier reflection on the half-plane where its real part is less than one. In the overlap, keep the chosen coordinate fixed and move along a separate affine line in the already extended coordinates. Near one point on that line all real parts are positive, so the common-strip identity applies. The identity theorem carries that identity back to the point under consideration. Thus the formulas agree on the overlap, and the extension is holomorphic along the required affine lines. Induction removes every restriction on the coordinate real parts.

This proves the analytic statement for the normalized diagonal Tate integrals in Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §7.1, proof of Proposition 7.1, p. 44.

The same construction gives `ComplexTateProductEntireFamilyStatement` for nonempty coordinate spaces. Its witness is one function of all exponents, with an entire restriction to every affine spectral line of real slopes.
