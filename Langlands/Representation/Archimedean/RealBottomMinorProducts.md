# Products of bottom minors in real principal series

This internal extension of `RealTiedMinorProduct` allows several minors of
different sizes. Each row set is a bottom segment. The product transforms
under the upper triangular subgroup by the product of the corresponding
diagonal coordinates. The source and target characters must differ by this
factor.

The product of compound matrices is multiplicative by Cauchy–Binet.
Differentiating its matrix entries in the right variable expresses each
derivative as a linear combination with the same row configuration.
Consequently the subspace of source vectors whose products all lie in a
given Lie-stable subspace is itself Lie-stable.

On `O(n)` the sum of the squares of the real coefficients in a given row is
one, by orthogonality and multiplicativity. Multiplying the compact
restriction of a target vector by each coefficient gives source sign
covariance, since the diagonal sign factor squares to one. The Iwasawa
extension of these compact functions gives a finite decomposition of the
target vector into products. `eq_top_of_cyclic` uses this decomposition and
a cyclic source vector to prove generation of the target by its products.
