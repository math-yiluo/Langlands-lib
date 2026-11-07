# Conditional descent through the actual Brauer presentation

Worker 1727 constructs linear descent from the explicit arithmetic hypothesis
`KernelCompatibility F e` and the existing normalized reciprocity premise.
This is internal quotient algebra for the existence task. The hypothesis remains
visible in every construction; no unconditional existence theorem is asserted.

`presentation_ker_le_evaluation_ker` rewrites the arithmetic assertion as a
kernel containment. `degreeZeroValue` descends evaluation through the quotient
by the presentation kernel and transports it along the first isomorphism
theorem, using the proved surjectivity onto the actual continuous exact
`DegreeZero`. Its presentation and generator formulas recover the actual
products of abelian ratios. Surjectivity proves uniqueness and Haar independence
of the descended map.

The published `CommonClosureSpectralAnalytic.haarMeasure_nonempty` obtains
regular additive Haar measures from positive
compact subsets of the actual locally compact field. `referenceMeasures`
chooses one on each intermediate field. That choice is used only in the
already proved Haar-independent descended degree-zero map.

`reducedVirtual` subtracts the actual integer degree times the trivial reciprocal
character line. Its image lies in the actual dimension kernel by the genuine
degree-one formula. `virtualValue` adds the descended reduced value to the
integer degree times the actual abelian unit for the trivial line. `assignment`
translates this integer-linear map back to complex units. Its additivity
is exactly linearity, and `assignment_formula` records its reduced-class
factorization. `assignment_haarScaling` uses proved abelian Haar scaling and
the integer power product rule; the degree-zero factor does not depend on the
supplied measure.

These definitions retain independent field and representation universes and
use the original continuous exact quotient. They do not prove rank-one
agreement or induction, and they do not remove the arithmetic kernel premise.
They follow the quotient-descent mechanism of Deligne §4.7 as an internal
algebraic construction; the source arithmetic identity remains separate.
