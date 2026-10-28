# Relative Jacquet finite-filtration multiplicity proof

`Langlands.glRelativeJacquetFiltrationMultiplicity` proves
`Langlands.GLRelativeJacquetFiltrationMultiplicityStatement` with independent
universes `uF`, `uV`, and `uW`.

The inner clause directly specializes
`Parabolic.normalizedOppositeJacquetFiltrationMultiplicity` to the smooth
coarse-Levi representation and its supplied filtration. The existing
`innerJacquet` bundler is the same actual normalized refined opposite
Jacquet construction, so this gives the required equivalence, including
actual finite composition-series witnesses in both directions.

For the ambient clause, the proof forms the actual
`Parabolic.normalizedInductionFiltration` of the outer normalized
induction, with the same original length and indices. The induced
representation is smooth by `T.isSmooth_normalizedParabolicInduced`.
The composed clause of the opposite Jacquet filtration multiplicity
theorem then expresses the whole multiplicity as a sum of actual
finite-series multiplicities for the composed opposite Jacquet of
each induced-filtration grade.

For each original index,
`Parabolic.normalizedInductionFiltrationGradedEquiv` identifies that
actual induced grade with the outer normalized induction of the
original coarse-Levi grade. A private helper descends this equivalence
through the normalized composed opposite Jacquet construction. It
uses the existing descended maps of the equivalence and its inverse;
their compositions are the identity on quotient classes, hence on the
whole quotients because each quotient map is surjective. The
normalizing character is unchanged.

`equivJordanHolderMultiplicityTransport` transports the actual
finite-series witnesses through each resulting representation
equivalence, leaving `τ` fixed by its identity equivalence. It works in
both directions. The family of natural counts and its sum equation
are retained verbatim, giving precisely the ambient clause on the
original coarse-Levi grades.

The opposite Jacquet multiplicity theorem supplies the actual-series
existence and summation in both directions. In the ambient application
its input carrier universe is `max uF uV`; the constituent universe
remains the independent `uW`. All original indices, empty sums,
repeated steps, zero grades, actual groups, and both factors of the
composed normalization are preserved. Smoothness is the only
representation hypothesis, and no additional finite-length,
admissibility, irreducibility, splitting, or exactness certificate is
required.

This is an internal derived proof from the actual normalized induction
filtration and opposite Jacquet finite-series results, with no separate
literature theorem claimed. It proves neither an inner-versus-ambient
constituent inequality nor equality of Weyl totals, positivity, quotient
detection, or an irreducible-head conclusion. Those host obligations
remain separate.
