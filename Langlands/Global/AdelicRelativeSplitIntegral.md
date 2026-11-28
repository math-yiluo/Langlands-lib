# Cancellation of the split Iwasawa density in the normalized shell integral

The radical-first Iwasawa formula weights the relative split Haar by the inverse parabolic modulus. At a relative positive split point, this modulus is the square of the half-modulus in `normalizedPairing`. The two factors cancel in the integral of the pairing, and in the integral of its absolute value.

The proof uses the identity for parameter powers under addition to square the half-modulus. The real Iwasawa density is the parameter power at the negative modulus parameter, so its complex value is the reciprocal of the squared half-modulus. The integral with respect to a density is the integral of its real value times the original integrand. After this substitution the reciprocal cancels pointwise. Taking absolute values gives the corresponding norm identity.

`relativeSplitIntegral` then changes variables by the projected coroot logarithm. Restricting the prescribed Haar to an arbitrary split set pushes to Lebesgue measure on the corresponding coordinate set, multiplied by the same positive scalar for every split set and integrand. This is the density cancellation and split Haar normalization in Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics 426 (2023), 109107, (7.7) and the weak shell integral following (7.23).
