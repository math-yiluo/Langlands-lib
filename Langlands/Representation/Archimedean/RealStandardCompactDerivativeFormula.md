# Compact differential formula for real standard modules

`RealStandardCompactDerivativeFormulaStatement` gives the restriction of a
scalar right derivative to the orthogonal group. For each size, block list
and matrix direction \(X\), it gives smooth complex coefficients on
\(GL_n(\mathbb R)\), independent of the standard vector. At each orthogonal
\(k\), the derivative is a scalar multiple of the value at \(k\) plus a
sum of derivatives in the coordinate directions \(E_{ij}-E_{ji}\) with
those coefficients.

For a matrix \(A\) representing \(k\), split \(AXA^{\mathsf T}\) into an
upper triangular part and a skew part using `upperPart` and `skewPart`.
The resulting expression for the tangent direction \(AX\) separates a left
upper triangular derivative from a right skew derivative. The left term
uses the exponential equivariance of the underlying normalized scalar
principal series. It multiplies the value by the shifted exponents paired
with the diagonal of the upper part. Conjugating the skew part back by
\(A^{\mathsf T}\) gives a skew right direction, which is half the sum of
its entries times the coordinate skew matrices. These matrix formulas
extend the coefficients smoothly to all of \(GL_n(\mathbb R)\). The
normalized scalar covariance holds for the full standard module, including
its subspaces with rank-two block Fourier conditions.

`rightDerivative_eq_of_eqOn_skew` transfers equalities on the orthogonal
group to their skew derivatives. The proof conjugates the right direction
to a left skew direction and applies the published tangent derivative
identity. For words, induction applies the first-order formula to the
derivative for the tail of the word. Skew tangency justifies differentiating
the induction identity along the compact directions. The product rule
keeps the old word when the derivative lands on a coefficient and prepends
a skew direction when the derivative lands on a vector term. The empty word
starts the expansion with coefficient one.

`exists_compactWordBound` applies the resulting finite expansion in the
actual compact Banach realization. The smooth equivalence represents every
genuine smooth vector by a scalar standard function. The identity for a
single derivative on `embed` iterates in word order. Each coefficient has
finite supremum norm on the compact group, and every compact word appearing
in the expansion belongs to the finite image of the word index. Summing
the coefficient norms times the sum of the norms for that finite set bounds
the original word seminorm uniformly over the entire smooth carrier.
