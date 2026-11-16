# Neutral field comparisons from a nonempty full-fibre open

Fix a represented relative identity component of the integral Chevalley closure.
Assume its integral group is smooth and affine with geometrically connected fibres.
For a field algebra, suppose a nonempty open of the full field fibre lies in the image
of the supplied closed field Chevalley embedding. Then the factor of that embedding
through the neutral fibre is an isomorphism.

The implemented proof pulls this open back along the neutral inclusion. The pulled
open is nonempty because every point of the original open comes from the Chevalley
group, whose embedding factors through the neutral inclusion. Injectivity of that
inclusion puts the pulled open in the range of the neutral field embedding.
The neutral fibre is smooth, connected and affine, hence geometrically integral by
the published smooth connected affine group geometry theorem, and therefore integral.
Its nonempty open is dense. The field embedding is closed, so its range is the whole
neutral fibre. A surjective closed immersion into this reduced scheme is an isomorphism;
reflection through the forgetful functors supplies the group-scheme isomorphism.

`neutralFieldIsoOfOpen` packages this actual comparison. Its composite with the neutral
inclusion is the original field embedding. Applying this criterion to all field algebras
supplies `HasFieldComparisons` for the same neutral family and full coordinate torus.
These internal deductions do not assume
that the full closure is connected, nor construct the required open or prove smoothness
of the closure. Those inputs remain explicit. No new literature input is used.
