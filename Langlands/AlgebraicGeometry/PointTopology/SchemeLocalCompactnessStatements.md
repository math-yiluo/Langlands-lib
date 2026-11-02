# Local compactness of locally finite type scheme points

This unit states local compactness for actual points of arbitrary locally
finite type relative schemes, using the explicitly constructed affine-chart
final topology. It preserves locally finite type, without a global finite-type
or separatedness premise.

## Source and exact target

Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), Proposition 3.1, printed page 4, asserts local compactness when the local
topological value ring is Hausdorff and locally compact, its units are open,
and inversion on the unit subspace is continuous. Remark 3.2 on that page
mentions the local-field and compact valuation-ring examples.
The registered source is `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

`Langlands.AlgebraicGeometry.PointTopology.SchemePointLocalCompactnessProperty`
has commutative rings `R` and `S` in a common arbitrary universe,
`Algebra R S`, and a topology only on `S`. It requires `IsLocalRing S`,
`IsTopologicalRing S`, `IsOpenUnits S`, `T2Space S` and
`LocallyCompactSpace S`. `IsOpenUnits` is separate from localness and says
that units with their existing value-and-inverse topology form an open
subspace of `S`.

The assertion quantifies over every actual relative scheme
`X : Over (Spec (CommRingCat.of R))` with `LocallyOfFiniteType X.hom`.
It concludes that the actual point carrier `RingPoint R X S`, equipped with
exactly `schemePointTopology R X S`, is a `LocallyCompactSpace`.
No topology on the base ring, separation of `X`, quasi-compactness, finite
presentation or global finite-type assumption is present. The conclusion
is local compactness, not Hausdorffness of this point space.

This is the derived relative form of the source's local-compactness assertion.
In each affine open of a locally finite type relative scheme the actual
coordinate algebra is finitely generated over `R`; finite coordinate
presentations with coefficients taking constant values in `S` give locally
compact point charts. Localness covers the actual point set by these charts,
and the open-unit/inversion hypotheses make the chart maps open embeddings.
These justify the relative form without requiring a topology on `R`.
Setting `S = R` recovers the source's formulation.

This contribution states the property and proves none of it. It neither
specializes the local-field/valuation-ring examples nor states the source's
separate Hausdorff, uniqueness, closed-immersion or fiber-product conclusions.
