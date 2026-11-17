# Simultaneous affine conjugacy from a split Borel vector series

Worker 591. This internal derived assembly implements the affine simultaneous
conjugacy argument in Conrad, *Reductive group schemes* (2014), Proposition
6.2.11(2), p.211, with the split Borel structural hypothesis still explicit.
The actual line-bundle Picard hypothesis is used throughout.

Over any affine scheme, a supplied global conjugator between two relative
Borels of a reductive group can be corrected to conjugate two supplied
closed split fibrewise maximal tori contained in those Borels simultaneously.
The proof factors the first torus, after the supplied conjugation, and the
second torus through the target Borel. The common-Borel torus conjugacy
theorem supplies a section of that Borel. Its image in the reductive group,
multiplied on the left of the initial conjugator, carries the first torus
to the second. Inner conjugation by that Borel section preserves the target
Borel, so the product retains the Borel range equality.

Over `Spec R`, assume a supplied `HasSplitBorelVectorSeries t`. The source
Borel in this presentation is globally conjugate to every relative Borel by
the published-input descent construction. Comparing two such conjugators
therefore conjugates any two relative Borels globally. No requirement that
the supplied Borels contain `t` is used for this Borel-only conclusion.

For the simultaneous conclusion, supply another split fibrewise maximal
torus `t'`, two relative Borels containing respectively `t` and `t'`, and
closedness of both torus inclusions. The preceding Borel result and the
correction construction give an actual group section conjugating both
represented ranges. `HasSplitBorelVectorSeries.simultaneousConjugatingPoint`
chooses it, and its specification records both full range equalities.
This module does not derive the vector-series presentation from
connectedness and Picard triviality; that structural input remains explicit.
