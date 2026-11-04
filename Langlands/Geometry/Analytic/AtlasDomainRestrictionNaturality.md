# Local characterization and naturality of unrestricted chart restrictions

This internal derived unit concerns the constructed bounded restrictions in an
arbitrary indexed affinoid atlas over a complete ultrametric normed field.
No directedness or greatest chart is assumed.

`intersectionCover` restricts an actual finite full-domain cover to a contained
full domain by literal full intersections. `glueChartRestriction_test` proves
the original restriction formula on every actual full-domain test contained
in a common original chart. On this intersection cover, the two inclusion
routes to the original target agree by full-domain uniqueness. The defining
local gluing equation and the original-chart overlap algebra-map theorem give
the desired formula on every member. Actual algebra separation proves it
globally.

This characterization proves equality of the entire bounded maps produced by
any two finite common-chart covers, and naturality for every actual original
full-domain inclusion, independently of the source and target cover choices.
`domainChartRestriction_test` and `domainChartRestriction_naturality` specialize
these statements to the chosen constructed maps.

`domainChartRestriction_of_commonChart` recovers the existing bounded formula
when the original local domain maps into a common original relative chart
domain. `domainChartRestriction_of_chartSubset` recovers the original
restriction followed by the unchanged domain's base map when the entire first
chart is contained in the second. In particular, `domainChartRestriction_self`
is exactly the original domain base map.

`domainChartRestriction_comp_original` proves composition with a containing
original target chart. It compares both maps on an actual finite common-chart
cover, uses the original atlas composition identity there, and applies the
local characterization and actual algebra separation.

Every equality is an equality of complete bounded algebra maps, including on
nonreduced algebras. The argument uses only the existing actual finite covers,
full intersections, full-domain uniqueness, original restriction composition
and separation APIs, with no new original-literature attribution. Arbitrary
positive radii, trivial valuations, zero quotients and permitted empty covers
are retained. General changes between three local-domain presentations,
the entire extended atlas and analytic or equivariant sites remain further work.
