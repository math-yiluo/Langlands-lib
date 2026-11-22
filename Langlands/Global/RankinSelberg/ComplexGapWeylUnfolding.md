# The quotient substitution in the alternate complex integral

`ComplexGapWeylUnfoldingStatement` identifies the actual complex ordinary
quotient integral of a Weyl-translated continued Godement value with
the integral on the alternate chart, assuming a split partial Fourier
test for the translated test and joint absolute integrability of the
displayed kernel. It retains the Weyl determinant character, the
Godement central sign and the positive chart Haar constant.

The proof inserts the fixed padded alternate restriction. The smaller
quotient variable is then right-translated by the inverse of the leading
matrix. Opposite Whittaker characters make the product independent of the
representative, even with the right translations in the two arguments.
Right invariance of the supplied quotient measure gives a
measure-preserving substitution for each chart point. Multiplicativity
of the determinant power moves the leading matrix's contribution into
the chart weight. Fubini leaves the smaller Whittaker pair on the inner
quotient, with the leading matrix translating the smaller vector.

`weylUnfoldedKernel_mk` records the evaluation on a supplied quotient
representative. The standard block inclusion agrees with padding
by the same number of identity coordinates.

This is the alternate expression in H. Jacquet, *Archimedean
Rankin–Selberg Integrals* (2009), §10.3, author p. 74, Lemma 10.3, in
the triangular Haar chart and positive Fourier convention of the
Library.
[Registered author edition](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
