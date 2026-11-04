# Bounded original-chart restrictions into contained local domains

This internal construction works with an arbitrary `IndexedAffinoidAtlas`
over a complete ultrametric normed field. It uses the original algebras and
bounded restrictions, with no directedness or greatest chart premise.

`originalChartRestriction_overlap` proves equality of the two actual bounded
maps from chart `j` into a full domain `W` over chart `i` whenever `W` has
actual inclusions into two original relative chart domains contained in
both charts. Compactness and the original net provide finitely many original
charts contained in both intermediate charts and covering the image of `W`.
Intersecting `W` with their original relative domains gives an actual finite
full-domain cover. On each member, full-test uniqueness for the original
restrictions identifies the entire bounded maps after composition with the
original `i` restriction. Original atlas composition identifies their maps
from `j`. Actual algebra separation on the finite cover proves the result.
Equality of spectrum-point functions is never used to identify algebra maps.

For any finite common-chart cover `c`,
`chartRestrictionFamily` consists of the actual structural maps of the
transported covering domains over `j`. The overlap theorem proves their
compatibility against every actual full-domain test into two members.
`glueChartRestriction` uses the published bounded-map descent construction to
glue those maps into the unchanged algebra of the original domain.
`restriction_comp_glueChartRestriction` retains each exact local composite.

`chartRestrictionFamily_chart` proves the original ambient chart equation
for each local map using the two original chart restriction equations and
the second quotient projection's structural triangle.
`glueChartRestriction_chart` proves that equation on every point of the
unchanged representing spectrum. The original full-domain exact image and
finite coverage provide a point of a covering spectrum above any given point;
injectivity of the original domain spectrum map identifies that lift's image
with the given point. The exact bounded-map gluing equation then identifies
its spectrum image with the local map's image. This use of spectrum points
proves only the chart equation; it does not identify algebra homomorphisms.

`domainChartRestriction` constructs such a bounded map for every full domain
over `i` whose ambient image is contained in chart `j`, by choosing the
constructed finite common-chart cover. No bounded restriction output is assumed.
`domainChartRestriction_chart` retains its ambient chart equation.

The provenance is the checked internal finite-cover, original full-domain
uniqueness, original restriction composition, actual scalar separation and
bounded-map gluing APIs. There is no new original-literature attribution.
The constructions include arbitrary positive polyradii, trivial valuations,
nilpotents, zero quotients and empty covers. Full representation over the
second original chart, independence, composition, unrestricted extended atlases
and analytic or equivariant sites remain further work.
