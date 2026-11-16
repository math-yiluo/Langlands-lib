# Finite compact chart covers as actual quasi-étale site covers

This internal construction packages the finite chart selection from
`QuasiEtaleFiniteChartCover` in the actual quasi-étale site over an arbitrary
localized analytic space. The field is complete and ultrametric; the space and
chart-index universes agree.

`FiniteCompactChartCover U` consists of a finite index type, actual objects of
the quasi-étale site, arrows to `U`, compact Hausdorff source spaces, a
surjective full chart on each source, and joint surjectivity of the arrows on
underlying points. Its presieve belongs to the defining quasi-étale
precoverage: the finite family of images of the full charts has union the
entire target space. Consequently its generated sieve belongs to the
quasi-étale topology.

For a site object whose underlying space is compact, choose a quasi-étale
strong representative and the arrow isomorphism supplied by its structure
property. The source isomorphism transports compactness to the strong source.
Select finitely many quasi-étale charts by the imported finite selection
theorem. Their composites with the target isomorphism are quasi-étale by
isomorphism invariance, so they are actual site objects over the original
base. Their maps to `U` are the domain inclusions followed by the source
isomorphism; the arrow isomorphism proves the triangles. Each source is a
compact chart-domain object with its imported full chart. The finite range
cover and surjectivity of the source isomorphism prove joint surjectivity.

This uses only proved domain, chart, and isomorphism results. It does not
assume general quasi-étale composition or base change. Refinements of
arbitrary covering sieves, finite nerve presentations, and the cohomological
comparison remain separate obligations.
