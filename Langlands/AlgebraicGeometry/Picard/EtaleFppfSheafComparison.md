# Comparing the etale and fppf sheaves of ordinary Picard classes

This internal construction applies the comparison of sheafifications for ordered
topologies to the published ordinary `RelativePicard.classPresheaf f`, for any
morphism of schemes `f : X ⟶ S`. Both topologies use the entire category
`Over S`. No restriction on the test schemes or on their sections occurs.

`etaleClassSheaf` is its sheafification for the big etale topology.
`etaleToFppfClassSheaf` maps it to the restriction of the exact published
`RelativePicard.classSheaf f` to that topology. The map is the unique extension
of the fppf unit along the etale unit. The equality
`toEtaleClassSheaf_etaleToFppf` records this factorization, and
`etaleToFppfClassSheaf_classOf` specializes it to the class of an actual bundle
on any base change.

`etaleFppfClassSheafIso` retains the explicit hypothesis that the underlying
presheaf of the etale class sheaf is an fppf sheaf. Under that hypothesis the
generic comparison has an inverse, also compatible with the two units. The
isomorphism is in the category of etale sheaves; its target has precisely the
underlying presheaf of the published fppf class sheaf.

The construction is derived from `SheafificationComparison.comparisonIso`, the
inclusion of the etale topology in the fppf topology, and the published ordinary
Picard presheaf and sheaf. It asserts no external literature theorem. In
particular it does not establish the displayed fppf sheaf hypothesis, even over
a field, and supplies no stack descent or representability. Those are separate
geometric obligations in the corrected Picard-stack route.
