# Faithful local representatives of arbitrary full field points

This internal construction works over a complete ultrametric normed
field `K` with a complete normed extension field `L`. The algebra,
space and extension-field universes are independent. Full-point
comparison retains the explicit domain completed-residue comparison.

On any chart containing two full field points, equality of their
bounded evaluations first identifies their underlying seminorms by
taking norms. The chart images therefore identify their underlying
points. The existing uniqueness of extension from a chart evaluation
then identifies every chart evaluation and the entire full points.
The chart-index universe in this comparison is independent as well.

For a presented affinoid algebra with spectrum small in universe `v`,
`SmallAffinoidSpectrum.chartMap` turns a bounded map from a chosen
target chart algebra into the original algebra into a complete strong
map to the saturated target. The target space and chart-index
universes are both `v`, as for the localized target statement.
The construction transports along the retained global-algebra equality
and applies the canonical global-chart source map. Its image lies
inside the chosen target chart and its global bounded pullback is
the supplied map, with exactly that algebra transport.

If the original algebra has bounded character `χ`, and composing it
with the supplied bounded map gives the selected evaluation of a
prescribed full target point, mapping the full character point gives
that prescribed full target point. The proof computes bounded
evaluation using the exact global pullback and uses the containing-chart
comparison above. It preserves the explicit completed-residue premise.

For each containing chart of a full point `p` on a saturated target,
`p.chartTestSource` is the saturated spectrum of the kernel quotient
of that chart's actual bounded evaluation. The chart's spectrum is
small in the original space universe because its chart map is
injective into that space; its quotient spectrum inherits the same
smallness. `p.chartTestPoint` is the faithful full point on this
quotient, and `p.chartTestMap` is the actual strong map defined by
the quotient map into that target chart. The map's image lies in
the selected chart. The preceding exact evaluation calculation
proves that it sends its full test point to `p`. Local evaluation
is quotiented by its own actual kernel; no faithfulness of the
original evaluation or global chart on the target is assumed.

The provenance is internal, from full-field-point chart extension and
the actual canonical strong chart-source maps. This unit does not
assert the final localized pullback preservation statement.
