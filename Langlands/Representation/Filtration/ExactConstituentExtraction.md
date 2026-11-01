# Irreducible constituent extraction through an exact smooth functor

Author: Worker 19.

This internal algebraic construction transports a finite filtration of an actual
smooth complex representation through a supplied functor preserving zero maps
and actual short exact sequences. It then extracts an irreducible coarse
constituent from an irreducible actual subquotient of the image.

The construction uses the existing image filtration of
`RepFunctorFiltration.exactSmoothTransport` evaluated on the constant smooth
functor. Each step is the invariant image of the mapped inclusion of the original
step. The existing exact graded comparison, evaluated at the sole object and
lifted to the full smooth category, identifies each actual smooth grade with the
image of the original smooth grade.

For a supplied composition series, the extraction theorem chooses a grade of
the image filtration containing the specified irreducible actual subquotient,
using `exists_smoothGradedObject_subquotient`. Exactness identifies that grade
with the image of a grade of the original composition series. The latter is
irreducible and is an actual subquotient of the original object. Finally,
finite module length supplies such a composition series. No finite-length or
admissibility assumption on the image object is required.

This is derived elementary module algebra, not a local rank-three product
calculation or either repeated-factor Jacquet transfer. The functor's exactness
and zero-map preservation are explicit lower-interface assumptions.

## Exact interface and universe scope

The groups `G : Type uG` and `H : Type uH` carry arbitrary supplied topologies.
Their universe levels and the carrier universe `uV` are independent. The
coefficient field is `ℂ`. The input and output objects use the same carrier
universe `uV`, as required by the actual smooth subquotient relation and the
supplied functor. The constructions and theorems do not require the carrier
universe to contain the group universes.

`onConstantSmooth` regards an object filtration as the filtration of the
constant smooth functor on `Discrete PUnit`. `exactSmoothImage` evaluates the
published natural image filtration at its sole object. Thus its actual steps
are ranges of the images of the original smooth inclusion maps; it does not
assume a filtration of the image. The initial and final steps and monotonicity
come from `exactSmoothTransport`. Zero-map preservation suffices for this
construction, and short exactness supplies `exactSmoothImageGradedIso`.

`smoothGradedObject_isSubquotient` uses the actual inclusion of the upper step
into `A` and its surjection onto the actual smooth quotient. The existing
injective/surjective presentation criterion proves that this grade is an actual
subquotient of `A`.

`exists_simple_grade_of_subquotient_image` assumes a supplied finite filtration
`s` with `s.HasSimpleFactors`. For any irreducible actual `D` occurring in
`J.obj A`, it returns an index `j`, irreducibility of the original smooth grade,
its actual occurrence in `A`, and the occurrence of `D` in the image of that
grade. The grades of the image filtration need not be simple or nonzero. The
first extraction theorem applies to their arbitrary actual smooth quotients.

`exists_irreducible_subquotient_of_image` assumes only `A.HasFiniteLength`,
zero-map preservation, the explicit generic short-exactness predicate, and the
irreducible occurrence in `J.obj A`. Mathlib supplies a composition series of
the module for `A`; the published length-criterion bridge pulls it back to an
actual representation filtration with simple factors. Applying the preceding
theorem returns an actual smooth `E` with
`E.IsIrreducible`, `SmoothRep.IsSubquotient E A`, and
`SmoothRep.IsSubquotient D (J.obj E)`. Neither `A` nor its image is assumed
admissible. No further structure of `J` is used.

## Dependency audit

The direct imports are `ActualGradedExtraction`, `ExactSmoothTransport`, and
`LengthCriterionProof`, all in `Representation.Filtration`. A recursive audit
finds 91 project modules including this module. Its classification-named imports
are exactly `ConstituentRelations`, `Segments`, `Supercuspidal`,
`SupercuspidalSupport`, and `SupercuspidalTwist`. They enter through the actual
subquotient presentation criterion in `ActualGradedExtraction`; that proof uses
ranges, kernels, quotient lifting and the first nonzero step, with no support
existence or uniqueness assertion.

`ExactSmoothTransport` proves its image and grade comparisons by functoriality,
actual kernels and ranges, and the quotient universal property. It uses
`Derivative.Mirabolic.MapsShortExactIntertwiners` only as the explicit assumption
on `J`; no derivative exactness conclusion is assumed as a proved input. That
predicate's import branch contains group and character definitions, local-field
normalization, smoothness and elementary twist proofs, and algebraic Whittaker
and localization constructions. It contains no classification proof used here.

`LengthCriterionProof.hasCompositionSeriesLength_of_compositionSeries` uses
only the invariant-subspace/submodule order isomorphism, covering relations and
actual quotient irreducibility. Mathlib supplies module composition series from
finite module length. This bridge neither asserts a representation finiteness
theorem nor invokes a cuspidal or segment classification.

Consequently this unit is independent of the eight classification tasks excluded
by the repeated-transfer contract and their conclusions: analytic strong-head
classification, multisegment exhaustion, ordered strong-head existence, general
ordered quotient coverage, tempered block uniqueness, square-integrable
classification, square-integrable exhaustion and regular exhaustion. It invokes
no global support decomposition or equivalent classification. This generic
extraction does not assert the local rank-three structure, ambient Jacquet
refinement, or either final transfer. Inspection of the final theorem reports
only `propext`, `Classical.choice` and `Quot.sound`, with universe parameters
`uG`, `uH`, `uV`; this is development evidence, not independent acceptance.
