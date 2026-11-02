# General affine-open point embedding proof

This proof helper supplies the affine-open part of
`Langlands.AlgebraicGeometry.PointTopology.SchemeOpenPointProperties`.
It works on the existing actual relative scheme-point carriers and affine
evaluation topologies. The hypotheses are a local commutative value ring `S`
with continuous multiplication and `IsOpenUnits S`; the coefficient ring has
no topology. No finite-type or separation premise is used.

`openOverHomOfLE` is the actual relative morphism between nested open
subschemes, using Mathlib's `Scheme.homOfLE`. Its composition with the ambient
open inclusion is proved to be the original inclusion. The existing
`continuous_affineSchemePointMap` from [AffineSchemeMapProofs](AffineSchemeMapProofs.md)
provides continuity of actual maps between
affine point spaces by naturality of the existing global-section point
homeomorphisms and continuity of coordinate precomposition.

For `isOpenMap_affineOpenPointMap`, take an actual point `p` of an affine open
`U` and a neighborhood of it in the point topology. Choose a basic open `D(f)`
of the ambient affine scheme contained in `U` and containing the image of the
closed point of `Spec S`. Localness and the already proved containment
criterion lift the whole point to `D(f)`. The point map `D(f) → U` is continuous
by the affine helper; its inverse image of the original neighborhood is open.
The actual point map `D(f) → X` is an open embedding by `AffineOpenPoints`.
Its image of this inverse image is therefore an open neighborhood in `X(S)`,
contained in the image of the original neighborhood. The equality of actual
postcomposition maps proves both containment and that this neighborhood
contains the original point.

These open neighborhoods at every point prove that `U(S) → X(S)` is an open
map. The existing injectivity and the affine continuity helper give
`isOpenEmbedding_affineOpenPointMap`. This is the general-affine-open step in
Conrad Proposition 3.1; the implemented proof exposes the basic-open cover
argument rather than assuming a gluing package.
