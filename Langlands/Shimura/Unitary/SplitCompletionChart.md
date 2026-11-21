# Oriented completion charts at split finite CM places

Let `K/E` be the given CM quadratic extension, `p` a split finite place of
`E`, and `q` one of the actual places above `p`. `SplitPlaceIdentification.oriented`
gives a split-center chart whose first factor is indexed by `q` and whose
second is indexed by `otherPlace q`. Its coordinate lemmas identify both
projections with `completedCenterMap` followed by the inverse of the
canonical completion embedding. In the chart, CM conjugation exchanges
the coordinates.

The construction numbers the two actual upper places using
`placesEquivFinTwo`. The published degree bound and positivity of both
local degrees force each degree to be one. The resulting completion
equivalences preserve the normalized valuations by the ramification formula.
Continuity uses the published completion embeddings and finite-dimensional
linearity for their inverses. In particular, the canonical identification
between the two upper completions preserves the valuation and is continuous.

The oriented chart uses the completed tensor product comparison, the two
degree-one identifications, and evaluation in the specified order. Every
algebra automorphism of the product of the base field with itself commutes
with exchange because exchange is the scalar trace minus the element. This
allows the original split chart's conjugation formula to transfer to the
oriented chart.

This is an internal comparison between the Library's completed-center
and completed-number-field constructions. It supplies the orientation for
Clozel's split-place local invariants from equation (2.3), printed p. 104.
