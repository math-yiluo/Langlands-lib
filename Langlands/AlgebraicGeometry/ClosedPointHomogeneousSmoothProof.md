# Proof of smoothness from transitivity on closed points

The theorem `Langlands.AlgebraicGeometry.closedPointHomogeneousSmooth.{u}`
proves the exact proposition
`Langlands.AlgebraicGeometry.ClosedPointHomogeneousSmoothStatement.{u}`:
every reduced scheme locally of finite type over an algebraically closed
field in the arbitrary universe `u` is smooth if its scheme automorphisms
over that field act transitively on its closed points. The empty scheme is
allowed.

Local finite type over the field makes the scheme a Jacobson space.
If the smooth locus is not the whole scheme, its closed complement
contains a closed point `x`. This also supplies a point of the scheme,
so the dense smooth locus over the perfect field is nonempty. Its openness
and the Jacobson property supply a closed smooth point `y`.
The transitivity hypothesis provides an actual scheme automorphism over
the base carrying `x` to `y`. The smooth locus pulls back along this
isomorphism to itself, because the composite structure morphism is
unchanged. Consequently `x` is smooth, a contradiction.

The proof adapts Andrew Yang's private Mathlib lemma
`AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed` from
`Mathlib/AlgebraicGeometry/Group/Smooth.lean`, pinned commit
`5ed2965256430c3649e86755f9576b54eca72435` (Apache 2.0).
It replaces the construction of translation automorphisms from a group
object by the explicit transitivity hypothesis and derives nonemptiness
from the hypothetical nonsmooth point. It uses no group law, torsion
cardinality, properness, characteristic-zero assumption, or density of
torsion points. Applying it to a torsion closure still requires proving
all its hypotheses on that actual scheme.
