# The Weyl translate of a complex Godement test

Right translation of a continued Godement value by the unfolding Weyl
element is the continued value of the right-translated rectangular test,
multiplied by the adjoining character at the Weyl determinant. The
determinant has normalized absolute value one. Associativity identifies
the two translated tests in the defining integral.

`ComplexGapWeylTranslationStatement` gives the translated test for every
rectangular Gaussian monomial. It fixes the leading columns and reverses
the remaining columns. The sum of the squared entry norms is preserved,
and `Finsupp.mapDomain` renames the exponents by the same permutation,
leaving the scalar coefficient unchanged.

These are the right-translation and test permutation used before the
quotient substitution in H. Jacquet, *Archimedean Rankin–Selberg
Integrals* (2009), §10.3, author p. 74, Lemma 10.3.
[Registered author edition](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
