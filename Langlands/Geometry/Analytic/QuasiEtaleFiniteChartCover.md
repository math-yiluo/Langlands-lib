# Finite compact chart covers in the quasi-étale site

This internal construction continues the local chart result in
`QuasiEtaleCompactCharts`. The field is an arbitrary complete ultrametric normed
field. Space and chart-index universes agree, as required by the existing
quasi-étale site.

A chart-domain object has an actual chart covering its entire space: take the
original chart, which is contained in its own range. Surjectivity follows from
membership in that range, with equality in the domain subtype.

For a quasi-étale strong map with compact source, the local factorization
condition supplies finite families of chart ranges with neighborhood unions.
Compactness selects finitely many such neighborhood unions. Their finite union
of families is still finite and covers the whole source. Choose the witnessing
chart index for each selected range. Each composite to the target is
quasi-étale by the local chart theorem, so these indices give finitely many
actual quasi-étale chart objects covering the source.

Actual site-cover packaging and transport to arbitrary localized
quasi-étale arrows remain separate obligations. Finite nerve presentations and the
cohomological comparison remain separate obligations.
