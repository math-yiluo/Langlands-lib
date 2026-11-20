# Naturality of localized affinoid tests

Let `K` be a complete nontrivially normed ultrametric field. The
`LocalizedAffinoidHomNaturalityStatement` records two composition laws for
the localized Hom comparison from actual affinoid spectra to the
analytifications given by finite polynomial presentations.
`localizedAffinoidHom_comp` identifies postcomposition by an induced
affine analytification morphism with precomposition by its algebra map.
`localizedAffinoidHom_precomp` identifies precomposition by the spectrum
map of a bounded algebra map with postcomposition by that algebra map.

The proof reads the composite strong maps on the whole-spectrum source
chart. For the first law it uses the composition formula for the
coordinate family of a strong map into an affine analytification. For
the second it composes chart pullbacks and transports the greatest-chart
pullback to the given bounded map. The extracted coefficients determine
the strong maps. Functoriality gives the two laws after localization.
These are internal consequences of chart-family comparison and the
localized affinoid Hom equivalence.
