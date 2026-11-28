# Isotropy of classical type D from its spin presentation

`numberFieldTotallyComplexTypeDSpinIsotropyReduction` proves isotropy over a totally complex number field for simply connected, absolutely almost-simple type D of rank at least four with a numbering whose nonfork vertices are fixed by the star action. The quaternionic case takes nonsingular isotropic rows at each completion for the skew Gram matrix of the spin presentation.

The spin presentation identifies split rank with the quadratic Witt index. The involution identifies the division algebra with its opposite, so its Brauer class has exponent dividing two. The number-field degree result gives division degree one or two.

In degree one the algebra is identified with the base field. Entrywise transport sends the polar matrix to the scalar polar matrix and preserves invertibility. The scalar form has dimension twice the absolute rank and is isotropic by the totally complex quadratic isotropy theorem. Pulling back a nonzero singular vector gives a totally singular line for the presented form.

In degree two the quadratic form gives a nonsingular skew-hermitian Gram matrix for quaternion conjugation. Given the local rows, `numberFieldHigherRankSkewIsotropy` provides a nonzero row with zero skew value. Equality of skew values with the zero row implies zero quadratic value. This again gives a totally singular line and positive split rank.

The argument formalizes the classical type D reduction in Platonov and Rapinchuk, *Algebraic Groups and Number Theory*, §6.6, Theorem 6.25, printed p. 352, using the quadratic and skew-hermitian isotropy arguments of that section. [Chapter 6](https://www.sciencedirect.com/science/article/pii/S0079816908620711)
