# Actual domain closure of the constructed enlarged atlas

This internal construction proves that taking further full affinoid domains
adds no new ambient subsets to the constructed enlarged atlas. It works over
a complete ultrametric normed field, with arbitrary independent original
chart and ambient-space universes.

`LocalDomain.extend` extends a full domain over a local domain's actual algebra
through its original full-domain representation. The existing proved
composition of full representations constructs this actual full domain over
the original chart. Its algebra is the unchanged inner domain algebra and
its structural map is the original bounded composite. Its exact locus is the
image of the inner locus under the original ambient map, and its ambient
spectrum equation is the actual composite spectrum equation.

`LocalDomain.pullback` applies this construction to an actual full-domain
inverse-image quotient along any supplied bounded coefficient map. Its
displayed locus is precisely the ambient image of the literal spectrum
preimage. No inverse-image representation is assumed as input.

For a chart of the enlarged atlas and any full domain over its algebra,
`saturatedDomainToLocal` constructs this extended original-chart local domain.
Its algebra is definitionally the same inner algebra, and its locus is
exactly that domain's image in the enlarged chart.
This gives one containment of the entire families in
`localDomainFamily_saturatedAtlas`. Conversely, every member of the original
local-domain family is already a chart domain of the enlarged atlas and
therefore belongs to its new local-domain family using the actual whole
domain of that chart. Thus the families are equal.

`HasAllLocalDomains` is the explicit equality between an atlas's family of
local full-domain subsets and its original chart-domain family.
`saturatedAtlas_hasAllLocalDomains` proves this property for the atlas already
constructed from actual algebras, maps and net data. The property is an output
of that construction. `HasAllLocalDomains.exists_chart` derives that every
actual local domain has an original chart with exactly its ambient subset
in any atlas satisfying this equality.

The derivation uses actual full-domain composition and inverse images, the
constructed enlarged chart choices, and the proved exact chart-family identity.
There is no new original-literature attribution, assumed saturation output,
peer draft, directedness or greatest-chart hypothesis. Arbitrary positive
radii, trivial valuations, nonreduced or zero quotients and permitted empty
domains are retained. General strong morphism gluing and composition,
atlas localization, analytic or equivariant sites and the Harris tower
remain further work.
