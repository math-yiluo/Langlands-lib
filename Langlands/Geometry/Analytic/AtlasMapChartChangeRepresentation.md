# Full affinoid domains under arbitrary chart change

This is an internal consequence of the constructed bounded chart change,
its coefficient-test universal property, and its exact reversal. It uses the
existing indexed affinoid atlas over a complete ultrametric normed field and
the actual finite positive-polyradius presented affinoid algebras.

For an original chart `i`, a bounded map `φ : a.algebra i → R` that fully
represents a domain `U`, and another original chart `j` containing the whole
ambient image of `φ`, `represents_changeMapChart` proves that the constructed
bounded change of chart fully represents the inverse image in chart `j`
of the ambient image. No inclusion between the two charts, saturation, or
directedness is required.

The range equation follows from the exact ambient chart equation and
injectivity of chart `j`. The locus is closed because it is the compact
image of the unchanged affinoid spectrum in a Hausdorff chart spectrum.
For the full universal property, an arbitrary presented affinoid test map
into the new locus is changed back to chart `i`. The original representation
then factors this map uniquely through `R`. Coefficient naturality and exact
reversal prove that this factorization recovers the original test map in
chart `j`. To prove uniqueness, the reversed coefficient-test law converts
any other factorization in chart `j` to one in chart `i`; the original
representation's uniqueness applies. These are equalities of complete
bounded algebra maps.

`changeMapChart_reverse_isMapChartChange` supplies the reversed universal
law used in that argument. It rewrites the canonical reversed chart change
by its already proved equality with the original map.

`changeDomainChart` packages the result for an actual `Domain` over chart
`i` whose ambient locus is contained in chart `j`. Its presented algebra
is literally the original domain algebra. Its structural map is the
constructed bounded chart change, and its locus is
`a.chart j ⁻¹' (a.chart i '' D.locus)`. The three accompanying equations
record these literal data. This unit constructs domain transport only;
quasi-isomorphism composition and localization are subsequent work.
