# Polynomial ordinary normalizations from real character presentations

`realOrdinaryPolynomialReduction` assumes exact ordinary continuation
and polynomial normalizations for real character lists. It gives polynomial
normalizations for adjacent-rank tests and equal-rank tests with standard
polynomial Gaussian rows, for arbitrary real block lists at scales `1` and
`-1` and with the supplied quotient measures.

An exact block coefficient belongs to the Whittaker model of the ascending
position-character presentation. The two test integrals agree because the
coefficient functions and the row are identical. Gamma recurrence expresses
the position denominator as the original denominator times a nonzero
polynomial. Multiplication of the entire original normalization by that
polynomial gives a normalization for the position presentation. Uniqueness
then identifies the product with the supplied position polynomial. For a
continuous quotient of two polynomials, each linear factor of the denominator
also divides the numerator. Cancelling such factors and extending the
cancelled identity by continuity gives a polynomial quotient.

The comparison and division implement the factor argument of §15, pp. 108–109.
[H. Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), author-posted
edition](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf#page=108)

The registered source is `jacquet-2009-archimedean-rankin-selberg`, SHA-256
`7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.
