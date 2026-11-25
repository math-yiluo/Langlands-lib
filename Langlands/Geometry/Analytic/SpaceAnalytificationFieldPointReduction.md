# Base-field points and the remaining analytification descent

This internal module proves injectivity of the underlying-point projection for
base-field-valued points of every affinoid atlas and every object of the
localized analytic category. It also constructs the field-valued point attached
to an algebraic rational point, conditional on the explicitly supplied
`AffineAnalytificationRationalPointsStatement.{u, u}`, and proves an equivalence
criterion for the remaining algebraic-space comparison.

The field has `NormedField`, `IsUltrametricDist`, and `CompleteSpace` instances
in the projection results. Their field, space, and chart-index universes
`u, v, w` are independent. The rational-point construction uses the original
nontrivially normed field hypotheses and common universe `u` of
`SpaceAnalytificationFieldPointsStatement`.

## Implemented projection proof

`fieldPoint_point_injective` applies `FieldPointSaturationComparison.fieldPoint_ext`.
For two field-valued points with the same underlying point, the spectrum points
in each chart agree because the chart is an embedding. Thus the two evaluation
characters have equal norms at every element. For an element `a`, subtract the
scalar equal to the first character's value at `a`. The first character vanishes
on this difference, and equality of norms forces the second character to vanish
there as well. Since both are algebra maps over the base field, their values at
`a` agree. `FieldPoint.ext'` then proves equality of the field-valued points.

Every localized object is the localization of a saturated presentation, via
`localizedObjectEquiv`. At that object, the localized projection is precisely
the atlas point wrapped in `ULift`. Applying `ULift.down` therefore reduces its
injectivity to the atlas result. No analytification or separatedness hypothesis
is used.

## Canonical rational-point map and equivalence criterion

`identityFieldPointOfAffineComparison` chooses the identity `K`-point in the
saturated affine analytification using the third clause of the supplied affine
comparison. Its projection is the constructed analytic identity point.
`rationalFieldPointOfAffineComparison` maps this point along `p K P₀ x`.
Naturality of `localizedFieldPointProjection` proves that its underlying point
is exactly `rationalPoint p P₀ x`. These constructions require only `PointFamily`,
without any analytification laws.

`fieldPointEquiv_of_rationalPoint_image` retains two further premises:
`rationalPoint p P₀` is injective, and every base-field-valued point projects to
some `rationalPoint p P₀ x`. The first premise proves injectivity of the canonical
field-point map. The second, together with the unconditional projection
injectivity, proves its surjectivity. `Equiv.ofBijective` supplies the desired
equivalence and preserves the already proved underlying-point formula.

This module does not prove these two premises, the affine comparison, or the
complete `SpaceAnalytificationFieldPointsStatement`. In particular, an étale
chart over a rational target point need not have a rational lift; the retained
image premise needs descent through a possible residue-field extension.

## Provenance

This is an internal derivation from the published `FieldValuedPoints`,
`SaturatedStrongLocalization`, `SpaceAnalytification`, and affine rational-point
statement interfaces. The scalar-subtraction argument is the elementary
base-field character argument described in the Markdown of the published
field-point statement `SpaceAnalytificationFieldPointsStatement`. It also
appears in the module `FieldPointSaturation`, whose
`FieldPointSaturationComparison.fieldPoint_ext` the projection proof above
applies.

The image argument is motivated by Conrad–Temkin,
*Non-archimedean analytification of algebraic spaces* (2009), Example 2.3.2,
printed pp.11–12, registered as
`conrad-temkin-2009-nonarchimedean-analytification`. That passage uses
residually trivial pointed étale neighborhoods and fibre products to identify
closed points while preserving residue fields. No completed-residue-field
comparison or descent result from that passage is claimed in this module.
