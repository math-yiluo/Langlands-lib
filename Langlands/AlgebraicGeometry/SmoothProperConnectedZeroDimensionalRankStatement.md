# Native endomorphism rank in relative dimension zero

`Langlands.AlgebraicGeometry.SmoothProperConnectedZeroDimensionalRankStatement`
is a proposition target for the dimension-zero boundary of the polarized
finite-flat rank problem. Let `K` be an algebraically closed field and let
`X` be an actual scheme over `Spec K`. Assume its structure morphism is
smooth of relative dimension zero, proper, and geometrically connected.
The proposition says that the structure morphism is an isomorphism and
that every actual over-endomorphism `f` has underlying scheme morphism
equal to the identity and native `Scheme.Hom.finrank` equal to one at
every target point.

The formulation uses the same actual over-scheme and native rank as
`Picard.PolarizedFiniteFlatRankStatement`. It needs no line bundle,
polarization exponent, finiteness or flatness assumption on the
endomorphism: these hypotheses become unnecessary in relative dimension
zero. In particular, its rank conclusion is the required `q ^ 0 = 1`
for every positive `q`, including `q = 1`, in arbitrary characteristic.

This is an internal derived interface. Mathlib identifies smoothness of
relative dimension zero with etaleness. Over a separably closed field,
the etale point-lifting theorem gives a rational section through a point
of the nonempty connected source. The open diagonal of the etale map
makes the section an open immersion, and properness supplies
separatedness, making the section a closed immersion. Its image is
nonempty, open and closed in a connected space, so the section and the
structure morphism are isomorphisms. Cancellation then identifies each
over-endomorphism with the identity. Mathlib's native rank of an
isomorphism is one.

This file states the interface only. It proves neither the interface nor
the positive-dimensional numerical polarized-rank formula.
