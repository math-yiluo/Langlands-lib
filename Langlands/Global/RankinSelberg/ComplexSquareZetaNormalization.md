# Entire normalization of the complex square zeta integral

`ComplexSquareZetaNormalizationStatement` takes an entire normalization of the independent complex Tate variables and constructs the corresponding entire function of the square zeta parameter. Its diagonal test is the upper triangular marginal of the Schwartz test averaged over right unitary translates with the standard vector as weight. Restricting the product Tate normalization to the affine line of inducing exponents shifted by `s` proves holomorphy. On the region where the square integral converges absolutely and every Tate exponent has positive real part, the product Tate reduction proves agreement with the zeta integral multiplied by the reciprocal Gamma product. The same positive measure factor works for every inducing list, vector, and test at that rank.

The module matches the diagonal normalization to `complexLFactor`, checks that reversing inverse data preserves its denominator, and identifies the product of shifted angular epsilon factors with `complexEpsilon` at the negative trace sign.

These formulas implement the entire normalization used in the square zeta functional equation. [Jacquet, *Archimedean Rankin–Selberg integrals*, §4.7](https://doi.org/10.1090/conm/489/09547).
