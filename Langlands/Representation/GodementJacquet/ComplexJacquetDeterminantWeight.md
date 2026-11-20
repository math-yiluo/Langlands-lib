# Determinant weights in the complex Jacquet recursion

The lemmas compute the determinant factors used in Jacquet's *Archimedean Rankin–Selberg Integrals* (2009), Proposition 7.3, p. 51. The determinant character is left as an arbitrary character of `ℂˣ`. The normalized determinant power uses the real logarithm of the squared complex norm. Its multiplication and exponent rules follow from the real logarithm and complex exponential identities. Inverse transpose inverts the determinant character and negates the absolute-value exponent.

`complexRectangularJacobian_jacquet` applies the two-sided additive Jacobian to the matrices `k⁻¹` and `g^ι`. The long Weyl matrices have determinant norm one, since each is an involution. The published adjacent-rank determinant recursion then gives the product of the two Weyl determinants as `(-1)^n` for ranks `n` and `n+1`.
