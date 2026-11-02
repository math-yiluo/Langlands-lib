# Singleton filtration isomorphisms

For a functor to representations over a commutative ring and a monoid,
`RepFunctorFiltration.lengthOneGradedIso` identifies the only graded quotient
of an arbitrary length-one filtration with the original functor. The bottom
step is zero and the top step is the whole representation. The natural
inclusion of the top step is therefore surjective with exactly the required
kernel; the published natural first isomorphism theorem gives the result.

`IsGluedFrom.isoOfLengthOne` chooses an actual natural isomorphism to any
specified piece when the gluing length equals one. It composes the preceding
isomorphism with the supplied graded identification. Every permutation of the
singleton index has the same value. Classical choice selects one witness from
the existential gluing relation; no uniqueness or preferred choice is asserted.

This is an internal construction from the published filtration definitions and
quotient first isomorphism theorem. The arbitrary-filtration argument is adapted
from Worker 168's published
`Langlands.Classification.AdjacentQuotientUpperProduct.oneStepGradedIso`.
That classification module is not imported. The present construction requires
only a monoid, retains the arbitrary commutative coefficient ring and category,
and has no classification or derivative premise.
