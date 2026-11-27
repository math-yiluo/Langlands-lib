# Local-to-global representation by skew-hermitian quaternion forms

Module: `Langlands.GroupScheme.Rational.NumberFieldSkewRepresentation`. It states
`Langlands.GroupScheme.Quaternionic.NumberFieldSkewRepresentationStatement` and proves it as
`Langlands.GroupScheme.Quaternionic.numberFieldSkewRepresentation`.

`NumberFieldSkewRepresentationStatement` concerns an invertible skew Gram matrix of quaternionic rank at least two over a number field. A prescribed nonzero alternating quaternion represented by the scalar-extended form at every completion is represented by the original form over the number field.

In rank two, apply binary skew representation (`numberFieldBinarySkewRepresentation`). In higher rank, append the negative of the prescribed value as a separate line. Each local solution extends to an isotropic row whose new coordinate is one. The higher-rank isotropy theorem (`numberFieldHigherRankSkewIsotropy`) gives a nonzero global isotropic row in the enlarged form. If its last coordinate is nonzero, divide by that coordinate to obtain the given value. If it is zero, the original form contains a nonzero isotropic row and represents every alternating quaternion. [Kneser, *Lectures on Galois cohomology of classical groups*, §5.10 proposition, p. 95 and Springer appendix, §3 Theorem 5.3.3, pp. 109–112](https://www.math.tifr.res.in/~publ/ln/tifr47.pdf)
