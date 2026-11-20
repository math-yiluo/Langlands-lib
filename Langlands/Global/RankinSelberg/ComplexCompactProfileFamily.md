# Complex standard sections with a fixed compact profile

`characterList` fixes the integral angular weights and varies the complex radial exponents. A compact profile is a continuous function on the unitary group whose right translates span a finite-dimensional space and whose left diagonal-phase covariance is the product of the angular characters. The radial character and the normalized Borel shift both have value one on unit phases, so the profile condition is independent of the radial exponents.

`standardSection` applies the published principal-series extension with the normalized Borel exponents. For every radial tuple, the extension belongs to the exact compact-finite standard module and restricts to the original profile. Conversely, `compactRestriction` sends any vector of that module to an admissible profile. Its right translate span embeds in the image of the finite group translate span under restriction. The Borel transformation law gives the phase covariance. The Iwasawa uniqueness theorem for standard functions with the same unitary restriction shows that extension recovers the original vector.

For positive Iwasawa diagonal entries \(\exp(\alpha_i(g))\), the extension is the fixed profile on the unitary factor times
\[
\exp\!\left(\sum_i 2\alpha_i(g)\left(p_i+\frac{n-1}{2}-i\right)\right).
\]
The factor of two comes from the squared complex norm. The continuous Iwasawa coordinates give joint continuity in the tuple and group argument. At a fixed group argument the exponential is the exponential of an affine complex-linear function of the tuple, giving joint holomorphy there.

This realizes the standard sections with fixed compact restriction in Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §7.1, p. 43, on the Library's compact-finite carrier. Reversing the source's lower-Borel indexing gives the upper-Borel shift used here.
