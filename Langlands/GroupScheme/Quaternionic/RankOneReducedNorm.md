# Reduced norm of a rank-one matrix update

`RankOneReducedNormStatement` applies to a central division algebra over a field and an arbitrary commutative scalar algebra over that field. For a column \(x\) and row \(y\) with scalar-extended division coefficients, the matrix reduced norm of \(1-xy\) equals the coefficient reduced norm of \(1-yx\).

Extend scalars further along the algebraic closure of the ground field. This map is injective and the reduced norms become ordinary determinants in the splitting charts. The chart of the column times the row factors as a rectangular scalar column block times a rectangular scalar row block. Their reversed product is the chart of the contracted coefficient. Applying the rectangular determinant identity \(\det(1-AB)=\det(1-BA)\) gives the result. The ground-field specialization follows by applying the formula to the original coefficients embedded as simple tensors.

The calculation supplies the reduced norm of the explicit reflection used for proper quaternionic Witt transitivity. [Kneser, *Lectures on Galois cohomology of classical groups*, §2.6 Lemma 2, pp. 32–33](https://www.math.tifr.res.in/~publ/ln/tifr47.pdf)
