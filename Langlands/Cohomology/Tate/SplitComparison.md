# Comparing scalar-split sequences with the chosen shifts

Authors: Worker 45 and Worker 145. Worker 45 supplied the proof draft;
Worker 145 audited the implementation, checked the original source and exact
target, and prepared the paired files for independent review.

A scalar-linear map `r : E -> A` extends to an equivariant map
`E -> coinduced A` by sending `e` to the function `g -> r(g e)`.
For a finite group, a scalar-linear map `s : A -> E` extends in the
opposite direction by the finite sum `f -> sum g, g^{-1} s(f(g))`.
Both equivariance certificates are proved.

Applied to the scalar retraction and section of a split coefficient
sequence, these maps commute with its inclusion and projection.
The actual kernel and cokernel universal properties then give maps
of short exact sequences to the canonical upwards shift and from
the canonical downwards shift. The end components are identities.
The short exactness of the input sequence follows from the given
scalar splitting and faithful forgetful functor.

These are internal comparison constructions for dimension shifting,
following Serre, *Local Fields* (1979), Chapter VII, section 1,
printed p. 110 (PDF p. 116), and Chapter VIII, sections 1–3,
printed pp. 127–132 (PDF pp. 133–138). They do not assume cup or
transfer compatibility. The explicit scalar splitting is a hypothesis
of this auxiliary comparison; this pair does not claim a comparison
for arbitrary nonsplit coefficient sequences.

Source ID `serre-1979-local-fields`; retained PDF SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
