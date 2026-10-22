# Conditional assembly of the normalized geometric lemma

This internal construction connects the published orbit-representative
replacement and actual support-image filtration to the existential conclusion
`GeometricLemmaTheorem`. Every geometric input remains an explicit hypothesis.
This module does not prove `PadicGeometricLemmaTheorem`.
Author: Worker 194, following Worker 164's assembly interface.

## Actual filtration

Fix a prime, an actual `PadicField F`, its compatible `TopologicalData T`,
and block shapes `B,C` of rank `n`. Given an actual finite ordered orbit cover
`s` and bijectivity of `parabolicDoubleCoset F.Carrier B C`,
`minimalParabolicSupportFiltration T B C s hBruhat` uses
`minimalPermutationOrdering` to replace the representatives by minimal
permutation matrices. It then applies `parabolicJacquetSupportFiltration`
to that replacement cover. Thus the result is an actual natural
zero-to-full filtration of `jacquetInductionFunctor`, with the same number
of steps as `s`. The imported replacement preserves the ordered orbit sets.
The convention is the orbit of the inverse permutation matrix.

The construction supplies neither the initial ordered cover nor Bruhat
bijectivity. It identifies no successive quotient.

## Conditional assembly laws

`geometricLemma_of_supportGraded` takes a finite enumeration of all minimal
permutations, an actual ordered cover, standard source and target refinements
for each minimal permutation, and all three subgroup equalities on both sides.
Its last hypothesis supplies natural isomorphisms from the successive
quotients of that cover's fixed support-image filtration to the corresponding
`geometricPieceFunctor` list.

The proof inserts these refinements, equality witnesses, enumeration and
filtration into the existing existential conclusion. It uses the identity
permutation in `IsGluedFrom`. It does not choose arbitrary associated graded
objects or replace natural isomorphisms by objectwise assertions. No separate
representative-compatibility premise is needed for this insertion lemma:
the supplied graded-isomorphism hypothesis already specifies every quotient
and its target functor.

`geometricLemma_of_orderedCosets` starts instead with any ordered cover and
the supplied Bruhat bijectivity. Its graded-comparison hypothesis applies to
every enumeration and ordered cover of the same length whose representatives
are the corresponding minimal permutation matrices. The proof obtains just
such an enumeration and replacement cover from `minimalPermutationOrdering`,
applies the graded comparison to them, and invokes the insertion lemma.
The witnessing filtration is therefore the actual filtration constructed by
`minimalParabolicSupportFiltration` for these inputs.

The field universe `uF` and representation carrier universe `uV` remain
independent; the ambient representation values have universe `max uF uV`.
The conditional construction works at every rank, including zero, because
it assumes its orbit, refinement and comparison inputs. This asserts no
unconditional extension of the positive-rank geometric lemma. No
admissibility, finite-dimensionality or finite-length assumption is added.

## Provenance and remaining obligations

Provenance is internal composition and existential introduction using
`OrbitRepresentatives`, `ParabolicSupportFiltration`, and their published
dependencies. There is no new literature claim. The implementation uses the
direct `HasGradedPieces` hypothesis and does not depend on an unpublished
graded-comparison statement.

Existence of ordered orbits, Bruhat bijectivity, actual standard-intersection
refinements, and the natural normalized graded comparison all remain
obligations for an unconditional proof. In particular, this module supplies
no compact-induction comparison, localization exactness, orbit quotient
isomorphism, or character cancellation. It is a conditional assembly unit,
not a proof submission for the main geometric-lemma target.
