# Actual affine intersections of Weil charts

This is derived infrastructure for the finite locally free Weil model used in
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011),
Example 4.2, printed pages 9–10. It supplies a canonical cartesian comparison for
the previously constructed affine-chart Weil scheme; it makes no assertion of
separatedness or of the full adelic comparison.

Let `A → B` be a finite projective extension of commutative rings, and let `Y`
be an actual scheme locally of finite type over `Spec B`. For original affine
opens `U` and `V` of `Y`, assume explicitly that their original intersection
`U ∩ V` is affine. No separatedness hypothesis on `Y` is required for this unit.

`affineChartWeilRestrictionIntersection_isPullback` proves that the existing
Weil restrictions of the two inclusion maps from `U ∩ V` form a cartesian
square with the original inclusions of the two affine Weil charts into the
actual glued Weil scheme. The compatibility equation is the existing chart
naturality law. Uniqueness follows from the open immersion into the first
affine Weil chart. For existence, equality in the glued scheme implies equality
of the two original counit comparisons in `Y`; the existing affine-intersection
lift and its two projection laws give the unique required morphism.

`affineChartWeilRestrictionIntersectionIso` is the associated canonical
isomorphism in the over category over `Spec A`, from the Weil restriction of
the actual intersection to the pullback of the two original chart inclusions.
The two named projection laws identify its composites with exactly the
existing Weil maps of the original open inclusions. This comparison is internal
derived geometry needed to study the diagonal of the actual Weil model.
