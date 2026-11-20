# Real approximation for connected affine groups over the rationals

`Langlands.GroupScheme.realApproximation` proves the published
`Langlands.GroupScheme.RealApproximationStatement`, Milne's Theorem
25.70 in *Algebraic Groups* (2017), p. 564. It gives density of rational
points in the actual evaluation topology on real points of every smooth
connected affine group over `ℚ`.

The proof applies the published characteristic-zero Levi reduction, so
it suffices to prove real approximation for connected reductive groups.
Transport a nonempty real open set to the points of the real base change
using the affine base-change homeomorphism. The density of points in
real maximal tori gives a point in this open set belonging to a real
maximal torus. Conjugation by any element of a sufficiently small real
identity neighborhood keeps the point in the open set.

The regular adjoint slice supplies a conjugator in that neighborhood
carrying the real maximal torus to the scalar extension of a maximal
torus over `ℚ`. Transport the chosen real torus point along the compatible
isomorphism of tori. Its image in the ambient group is still in the open
set. The inverse image of the open set under the rational torus inclusion
is thus a nonempty open subset of the real torus points. Real approximation
for rational tori supplies a rational torus point there, whose image is
a rational group point in the original open set.

Milne's proof uses a central cover and number-field cohomology in the
reductive step. The Lean proof uses local real openness and regular
Lie-element centralizers for this step.
