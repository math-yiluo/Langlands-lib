# Scalar descent for finite iterated Laurent covers

This proof establishes `IteratedLaurentScalarDescentStatement` using the
published unconditional binary Laurent gluing theorem on every presented
base, actual rational quotient comparisons, and formal transport of descent.

The private intersection comparison identifies the actual quotient of
`d.inter e` with the actual pullback of `e` over `d.algebra`. It composes the
relative equivalence for the first intersection inclusion with the bounded
equivalence of equal loci supplied by the published
`StandardRationalLaurentReduction.locusEquiv`. Its structural map and two restriction squares
follow from the published rational universal properties.

The private composition lemma takes a family `D` with scalar descent and a
family `E` with scalar descent after every bounded base change. It proves
descent of the family of actual intersections `D i.inter E j`. On each
`D i` quotient, it transports the intersection sections by the proved
comparison and applies descent of the pulled-back `E` family. This produces
a section on every `D i`. On each pairwise intersection of the `D` family,
the pulled-back `E` family separates elements. The actual triangle comparison
maps transport the lift equations there, and original compatibility makes
the two images equal. The `D` sections are therefore compatible and descend
to the base. The same comparison verifies the original equations and
uniqueness. All descent and separation in this formal composition are
explicit premises or consequences of the stated universal descent premise.

For zero Laurent functions the unique leaf is the actual `whole` quotient.
The published whole evaluation and its inverse equations give unique scalar
lifting. The successor step applies the formal composition lemma to the
first binary Laurent family and the remaining iterated family. Binary
descent supplies the first premise. The induction hypothesis on every
presented base supplies the universal tail premise, using the actual
equal-locus leaf pullback identification. An explicit equivalence between
Boolean functions on `Fin (m+1)` and a head Boolean paired with a tail
Boolean function reindexes the result to the chosen recursive leaves.

Finally, after any bounded map `P → Q`, the pulled-back leaves have exactly
the loci of the iterated leaves of the image tuple on `Q`. Formal
equal-locus transport gives the precise universal target. No analytic
refinement-descent assumption is used.

Achinger, *Introduction to non-Archimedean Geometry*, November 22, 2020,
Corollary 7.1.2, p.65 motivates the finite iteration. The retained source and
fingerprint are recorded in the statement Markdown. This implementation is
its scalar degree-zero specialization and allows every complete ultrametric
scalar field because the binary theorem used here is unconditional.
Worker 84 authored the iterated cover construction; Worker 101 authored the
formal reindexing and equal-locus transport; Worker 146 contributed the
formal compatibility preparation. Worker 572 wrote the composition argument
and induction.

The implementation retains the actual quotient carriers and all Boolean
leaves, including empty leaves. It covers zero and nonreduced bases, the
zero-length tuple, and trivial scalar valuation. Its conclusion is unique
scalar descent at unit radii, with no assertion of higher Cech exactness,
admissibility, finite-module descent, or arbitrary radii.
