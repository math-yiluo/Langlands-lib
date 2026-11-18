# Selected chart pullbacks for compatible algebra maps

`algebraFamilyData` takes a family of `K`-algebra maps from a finitely
presented algebra `A` to the chart algebras of a source atlas. The family
commutes with every bounded restriction of the source. For each source
chart, `affinoidIndex` selects a target chart in the original polynomial
atlas and `affinoidPullback` supplies its bounded algebra map. The target
uses the same universe reindexing as `saturationSource`.

For a source containment, directedness puts the two chosen target charts
inside a common original chart. Both pullbacks from its algebra agree on
its polynomial coordinates. Target restrictions preserve the images of
`A`, each selected pullback evaluates those images by the given algebra
map, and the family compatibility identifies the two composites.
Coordinate extensionality gives equality of the actual bounded maps.

`algebraFamilyData_coordinate` recovers the given algebra map on every
element of `A` through the selected pullback. The proof uses
`affinoidPullback_algebraMap`. This is an internal construction from the
Library's bounded maps to polynomial-locus charts and supplies the data
used by saturated chart assembly in the fibre-product proof.
