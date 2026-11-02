# Consecutive flattening of actual nested product induction

Author: Worker 320.

`flattenedSmoothFamily` lists a supplied nested family of actual smooth
representations in the existing consecutive flattened block order.
`flattenedProductInducedEquiv` gives an actual equivariant linear equivalence
from the normalized product induction of that family to the outer normalized
product of its inner normalized inductions.

This is an internal specialization of the published
`orderedRefinementTensorInductionEquiv`. The existing flattened block equivalence,
size equalities and coordinate identity provide its geometric data.
The regrouped factors equal the original supplied factors: cancellation of
the block equivalence identifies their dependent indices, and the size
transport affects only the rank index. Thus its nested tensor target is
the actual tensor of the supplied inner inductions.

The equivalence uses the same upper parabolics and normalized functors
throughout. It adds no representation-theoretic hypotheses, segment
identification or analytic assertion.
