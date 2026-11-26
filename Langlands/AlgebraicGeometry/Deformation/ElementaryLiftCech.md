# Čech differences and gluing of elementary lifts

Let `I` be a proper ideal of a local ring `R` with maximal ideal `m` and
`mI = 0`. The prescribed map is defined over `Spec R` from the quotient base
change of the source. If the target is smooth over `Spec R`, the map lifts
on every affine source chart. Restricting a local lift induces the
corresponding restriction of its reduced map. For an affine cover with
affine pairwise intersections, local lifts that agree on those intersections
glue over the base. The resulting reduction is checked on the affine
quotient charts.

For the coordinate lemmas the source is smooth over `Spec R`. Thus its
affine chart rings are flat, so the extended ideal on a chart is the scalar
extension of `I` to the residue chart. Choose a group law on the target's
residue fibre and finite bases over `R/m` of `I` and the cotangent space at
the identity, using an affine neighbourhood of the identity. With these
choices the difference of two affine lifts is a tuple of actual section
functions on the corresponding open in the residue fibre. These functions
restrict along open inclusions and pull back along morphisms between smooth
sources.

The Čech lemmas also assume the source is separated over `Spec R`, so the
intersections of affine charts are affine. On each triple intersection the
successive differences add to the total difference, giving the cocycle
identity. If the cocycle on an overlap is the first chart's correction
minus the second chart's correction, adding the corrections to the local
lifts makes them agree on that overlap.

This is the affine torsor and gluing argument of SGA 1, Exposé III,
Proposition 5.1 and Corollary 5.2. In the elementary Artinian setting the
residue-fibre group supplies the constant coefficients used in GIT,
Proposition 6.15.
