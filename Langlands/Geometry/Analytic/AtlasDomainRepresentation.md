# Full representation in arbitrary containing original charts

Work with an arbitrary `IndexedAffinoidAtlas K X` over a complete ultrametric
normed field. Each original chart has an actual finite positive-polyradius
affinoid quotient algebra, and its contained-chart restrictions satisfy full
representation against every presented affinoid test. There is no directedness
or greatest-chart assumption.

For a full domain `U` over original chart `i`, `domainChartLocus i j U` is
the literal preimage under chart `j` of the ambient image of `U` under chart
`i`. Given a constructed finite common-chart cover `c`, the earlier
`c.glueChartRestriction` is an actual bounded map from chart `j` to the
unchanged algebra of `U`. This module proves its full representation of
that literal locus, including closedness, exact spectrum image, and unique
bounded factorization for every presented affinoid test.

The existing chart equation and the original domain's exact spectrum image
give `range_glueChartRestriction`. In the converse direction, a point of the
literal locus lifts to the original representing spectrum; injectivity of the
second chart identifies its image under the glued map with the requested
point. `rightChartDomains_cover` uses the original finite cover and the exact
ambient image of each transported member to cover the literal locus in
the second chart.

`overlap_firstBaseMap` considers any full domain over chart `j` with actual
inclusions into two transported covering members. Composing these inclusions
with their maps to the common original charts makes the original-chart
overlap theorem apply with the two ambient charts exchanged. The second
quotient projections' structural triangles then identify the original maps
from chart `i`.

`firstBaseMap_eq_of_secondBaseMap_eq` extends this to an arbitrary presented
affinoid target and two bounded maps from the covering algebras that agree
on the second-chart coefficients. Their common test map factors through the
actual full intersection over chart `j`. Original full-domain uniqueness
identifies its two composites with the supplied maps. Composing the preceding
overlap equality with this test factor proves agreement on the first-chart
coefficients. `restriction_eq_of_secondBaseMap_eq` then uses the original
full representation of `U` to identify the complete maps from `U.algebra`.
These are algebra-map equalities and retain nilpotents.

For an arbitrary test map `φ` from chart `j` with image in the literal locus,
`testCover` pulls back each transported full domain along `φ`. These actual
pushout quotients form a finite full-domain cover of the whole test spectrum.
Their covering restrictions are their actual structural maps.
`testLocalMap` composes each original restriction from `U.algebra` with the
second quotient leg of that pullback. The original pushout squares show that
these maps agree on the second-chart coefficients after every full-domain test
into two cover members. The preceding equality theorem therefore proves
`testLocalMap_compatible`. Actual bounded descent constructs `testFactor`.
Its local composite equations, the original chart-restriction gluing
equations and the pushout squares prove `testFactor_comp` by actual algebra
separation on the test cover.

Uniqueness does not assume representation of the new map. For any competing
factor, `factor_chart` derives its ambient chart equation from its factorization
equation. On each pulled cover member this places its spectrum image in
the original relative domain over `U.algebra`, using the exact transported
ambient image and injectivity of the first chart. That existing full relative
domain gives a local factor through the corresponding original cover algebra.
Full representation of the transported domain over chart `j` identifies
that local factor with the actual second pullback quotient leg.
`factor_local_eq` records the resulting complete bounded map identity.
Separation, equivalently uniqueness of the bounded descent, proves
`testFactor_existsUnique`.

`represents_glueChartRestriction` combines this all-affinoid factorization
with the exact image. The locus is closed because it is the range of the
continuous map from the compact affinoid spectrum into the Hausdorff
second-chart spectrum.

`domainChartRestriction_represents` specializes to the constructed common-chart
cover chosen from the compact image of `U` and its containment in chart `j`.
`domainInChart` stores the resulting actual full domain over chart `j`.
Its algebra is definitionally `U.algebra`, its structural map is precisely
the constructed `domainChartRestriction`, and its locus is precisely
`domainChartLocus`. `chart_image_domainInChart` proves that its ambient image
is exactly the original ambient image of `U`.

The field may be trivially valued, radii need not be strict, and quotients
may be nonreduced or zero. Finite covers may be empty when coverage permits.
No new domain representation or bounded factorization is supplied as an input.
The construction is internally derived from actual common-chart covers,
original full-domain uniqueness, bounded map descent, literal full intersections,
and actual inverse-image quotients. It makes no new original-literature
attribution. Independence and coherence of unrestricted restrictions, the
entire extended atlas and its net, analytic or equivariant sites, and the
Harris tower remain further work.
