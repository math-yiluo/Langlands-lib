# Density of points in real maximal tori

`RealToralPointsDenseStatement` asserts that real points lying in a maximal
torus defined over `ℝ` are dense in the actual real points of every affine
connected reductive group over `ℝ`. The topology is the evaluation topology.

For a connected reductive group in characteristic zero, a rational point
belonging to a maximal torus after passing to the algebraic closure already
belongs to a maximal torus over the original field. Its centralizer contains
that geometric torus in its identity component. A maximal torus of the
identity component therefore has full geometric rank and is maximal in the
ambient group. The original point centralizes this torus and hence belongs to it.

Over the algebraic closure, the conjugation map from the product of the group
and a maximal torus has image containing a dense open subset. Rational points
in this open lift to actual points of the product. They therefore belong to the
conjugate torus specified by the lift.

For a nonempty real open subset of the group, unirationality gives Zariski
density of its underlying points. The field-extension projection is open,
so the inverse image of these underlying points meets the geometric
conjugation open. Every point in the inverse image over a real rational
section is the underlying point of its scalar extension. The first argument
then puts the chosen real point in a real maximal torus.

This internal step uses the published Cartan conjugation density and
maximal-torus centralizer results.
