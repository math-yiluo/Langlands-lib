# Gluing actual admissible charts, conditional on effective descent

Author: Worker 1726.

This internal module constructs the smooth parameter scheme and its actual
universal closed torus family from the supplied open charts and field coverage,
under the explicit hypothesis `HasEffectiveAdmissibleDescent G`.

First, `exists_universal_of_representableBy` takes a representing object for the
small relative presheaf. Decode the section corresponding to the identity of
the representing object and choose its actual closed relative-torus
representative. Naturality of the representing equivalence and the actual
restriction identity identify evaluation of this family on every relative test
with that equivalence. Its surjectivity and injectivity give respectively
existence and uniqueness in `IsUniversal`.

`totalSheaf` uses effective descent and the established full big Zariski
sheafness theorem. `glueDatum` is Mathlib's actual scheme gluing datum: the
supplied chart schemes, represented open intersections, and their canonical
transition maps. The chart maps are relatively representable open immersions;
field coverage gives local surjectivity of their coproduct. Mathlib's
`Scheme.LocalRepresentability.representableBy` therefore represents the total
presheaf by the scheme glued from these charts.

For `exists_smooth_universal`, take the base map from the total universal
section. The value of the representing equivalence on each open chart
inclusion is the chart's actual section; its first component proves that this
inclusion followed by the base map equals the chart's specified base map.
Smoothness follows by locality on the source using the glued scheme's actual
open cover and smoothness of every supplied chart. The total-presheaf
representation induces a representation of the relative presheaf over this
base map, and the first construction produces the actual universal closed
torus family.

All equivalences, restrictions and universality assertions hold on every
scheme test in the arbitrary universe `u`. The gluing construction is the
existing Mathlib scheme-gluing theorem applied to the actual admissible
presheaf, not a supplied moduli scheme. Effective admissible descent remains
an explicit premise; this module alone does not prove `ChartGluingStatement`.
