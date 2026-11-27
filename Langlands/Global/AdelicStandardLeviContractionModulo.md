# Standard Levi contraction modulo the outer unipotent radical

Consider a simple root of an upper standard Levi and the ambient maximal
parabolic omitting that root. A compact prefix in the minimal parabolic
normalizes both the ambient maximal radical and the outer radical of the
upper parabolic. Conjugated archimedean points in the maximal radical
therefore have a compact set of inner factors by
`adelicStandardLeviUnipotentFactors`. The inner factors lie in the
maximal radical of the upper Levi for the same root.

The smooth polynomial coordinates of `adelicMaximalUnipotentContraction`
give a bound for the next conjugation by a positive torus point. The
required simple-root lower bounds are those in the upper Levi. Projecting
to the archimedean factor and applying the closed embedding of the Levi
gives the right displacement in the ambient group. The remaining factor
conjugates into the outer radical on the left, giving the hypothesis of
`AdelicUnipotentDecayModuloStatement`.

`exists_standardLeviContractionModulo_normOne` also shows that every
right displacement lies in the archimedean part of the ambient norm-one
group. Inserting identity at the finite places commutes with the composed
embedding of the inner radical and the upper Levi. The resulting adelic
point belongs to the closed image of the smooth connected unipotent
radical. Its compact rational quotient forces the restriction of each
ambient character norm to be trivial.
`exists_standardLeviContractionModulo` gives the contraction estimate
on the ambient adelic group.

This is the contraction step for the estimate of the alternating constant
terms in Arthur 2005, §13, after (13.7), printed pp. 71–72.
