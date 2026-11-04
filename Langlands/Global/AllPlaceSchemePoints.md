# Actual all-place components of adelic scheme points

Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed p.10, Example 4.3, compares adelic projective points with the
full product of local projective points. This module constructs the actual
comparison map and its target topology for arbitrary schemes over either
kind of global field. The packaging and intrinsic naturality statements are
derived; the proper and projective homeomorphism assertions remain separate.

`CurvePlaceLocalPoints` is the product, over all actual curve places, of
`RingPoint F Y (curvePlaceCompletion v)`. The curve constants k are perfect
and F is a function field over k with the compatible supplied RatFunc
k-algebra structure. This includes positive characteristic global fields.
`NumberFieldLocalPoints` is the product of all infinite local point spaces
and all finite local point spaces for an arbitrary number field K. Both
branches allow any scheme Y over the original field, including nonaffine
and nonseparated schemes, in an arbitrary common universe. No finite type
or properness hypothesis enters these constructions.

The two `LocalPointTopology` definitions use the ordinary product of the
already constructed `schemePointTopology` on each factor, independently
of the adelic comparison map. Local points here are relative morphisms
over the original field. The existing `ringPointBaseChangeEquiv` and its
proved topological comparison identify these with points of the actual
local base changes; the value rings and schemes are not auxiliary models.

`curvePlaceAdeleProjection`, `numberFieldInfiniteAdeleProjection` and
`numberFieldFiniteAdeleProjection` equip the original adelic coordinate
ring maps with their compatible field-algebra structures. The two
`AdelePointMap` definitions change coefficients along precisely those
projections. Their displayed underlying-morphism formulas are actual
precomposition by the corresponding maps of spectra. Naturality follows
from associativity of morphism composition.

Local postcomposition by a scheme morphism is continuous for the product
topologies: each coordinate is the published continuous scheme point map.
The lemmas with suffix `_charts` additionally prove continuity of the
adelic coordinate maps when the source carries its affine-chart final
topology, by coefficient continuity and the product universal property.
These particular lemmas concern that explicitly named chart topology on
the nonlocal adele ring. The source's adelic topology is instead the
published `SpreadAdelePointTopology` obtained from arithmetic levels.
Continuity for that topology, its independence of a spread, and the
proper-scheme full-product homeomorphism are not asserted in this unit.
