# Exact classes of continuous representation filtrations

This internal construction uses the existing actual exact quotient and the
existing actual object filtrations. The group universe and representation
carrier universe remain independent. The assumptions are only `Group G` and
`TopologicalSpace G`.

`FiniteRepresentation.continuousFiltrationGraded` bundles the actual quotient
of consecutive invariant subspaces as a continuous finite-dimensional complex
representation. Its continuity follows from the actual surjection onto the
quotient and continuity of the upper invariant subspace, using
`SubquotientContinuity`. No invariant complement is assumed.

`exactClass_eq_zero_of_subsingleton` uses the actual short exact sequence
from a zero object to itself and then to itself to show its exact class is zero.
`exactClass_eq_subrepresentation_add_quotient` applies the defining exact
relation to the actual inclusion and quotient map.
`exactClass_subrepresentation_bot` and `exactClass_subrepresentation_top`
identify the endpoint classes; the latter uses an actual invertible
intertwiner.

`exactClass_filtration_step` applies the exact relation to the inclusion of
consecutive invariant subspaces and the published actual graded projection.
Exactness follows by identifying the kernel of the quotient map with the
image of the inclusion. `exactClass_eq_sum_of_filtration` then telescopes
these identities by induction over finite prefixes of the filtration.
The argument applies to arbitrary finite zero-to-full filtrations, including
the empty filtration of a zero representation, and requires neither simple
factors nor semisimplicity.

The proof follows the finite-prefix induction already used for representation
length in `Langlands.Representation.Filtration.RepresentationLength`, replacing
length additivity by the defining exact-class relation. This is derived internal
linear algebra and finite-sum bookkeeping; no new literature claim is made.
It supplies a prerequisite for the exact realization comparison and does not
itself prove bijectivity or existence of composition series.
