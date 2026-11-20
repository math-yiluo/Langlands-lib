# Local approximation of real maximal tori by rational maximal tori

`RealMaximalTorusApproximationStatement` takes a connected reductive group
`G` over `ℚ`, a maximal torus of its real base change, and an open
neighborhood of the identity in the evaluation topology. It gives an
actual real conjugator in that neighborhood and a maximal torus of `G`
over `ℚ`. The scalar extension of the rational torus agrees with the
conjugated real torus by an isomorphism compatible with the inclusions.

Use finite Lie coordinates of `G` and extend them to `ℝ`. In the adjoint
slice through the real torus, choose a parameter in the polynomial
nonvanishing locus of the regular slice theorem. The differential is
surjective at the identity and this parameter. Tangent smoothness gives
an affine open chart there on which the slice is smooth.

Restrict the chart on real points to the prescribed identity neighborhood
in the group coordinate and to the polynomial nonvanishing locus in the
slice coordinate. This is a nonempty open set. Smooth openness and the
homeomorphism from affine space points to finite coordinate vectors give
a nonempty open image in the real Lie coordinates. Coordinatewise density
of rational numbers produces a rational Lie element in that image.
The centralizer descent theorem applied to this element and its chosen
real lift supplies the rational torus and the compatible isomorphism.

This internal result uses the regular adjoint slice, complete-field smooth
openness, and regular Lie-element centralizer descent.
