# Joint finiteness of genuine scalar orbit coefficients

Worker 94 proves an internal algebraic finiteness step for orbit density.
The scalar coefficient construction and its actual derivative identity
are imported from the published `ArchimedeanScalarOrbitDifferentiation`
module. Their independently published contributions retain their own
authorship. This helper constructs the joint intertwiner and transfers
finiteness; it does not itself prove density.

The complex linear coefficient map is composed with the inverse of the
published `toSmooth` equivalence to obtain an endomorphism of the actual
`SmoothFunctions`. The genuine all-enveloping identity says exactly that
this endomorphism commutes with every enveloping operator. Consequently it
is an actual intertwining map for the published joint representation of the
center and compact enveloping subalgebra.

The published finite-vector map theorem takes the finite joint orbit of
the original vector to a finite joint orbit of its coefficient. This proves
`isJointFinite_smoothOrbitCoefficient` without any finite-dimensionality
assumption on the ambient smooth-function space. It adds no assumption
about analyticity, components, group translates or reproduction and does
not assert the final density or growth theorem.
