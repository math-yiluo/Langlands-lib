# Coherent reexpression of local full domains in original charts

For an arbitrary indexed affinoid atlas over a complete ultrametric normed
field, this internal construction proves coherence of the constructed bounded
chart restrictions. It imposes no directedness or greatest chart assumption.

`domainChartRestriction_extendDomain` proves that extending a local domain
along an original contained-chart restriction does not change the constructed
map from any other original chart containing its ambient image. Choose an
actual finite common-chart cover of the original local domain. Each member
extends to the larger original chart with its unchanged algebra and target
restriction. Original atlas composition constructs its inclusion into the
corresponding common original relative chart domain, retaining the original
second quotient projection. The all-test local restriction formula gives
the same bounded map on that member, and actual algebra separation proves
the global equality.

`domainInChartInclusion` retains every original full-domain inclusion's
entire bounded restriction after reexpression in a common containing chart.
Its structural equation is the proved source naturality.

`domainChartRestriction_reexpression` proves that moving a domain from chart
`i` to chart `j` and then to chart `k` produces exactly the same structural
bounded map as moving directly from `i` to `k`. Take the constructed cover
of the original local domain by intersections with common original charts
contained in both `i` and `j`. Each transported covering domain over `j`
maps to the reexpressed target with exactly the original covering restriction,
by the local gluing equation. Source naturality and the preceding original
extension theorem identify the composite with the restriction of the localized
domain in its common original chart.

On the original `i` side, source naturality first gives the map of the original
intersection member. The existing localization round-trip isomorphism has
identity restrictions on that algebra. Naturality under this isomorphism and
the original extension theorem identify its map with the same localized
common-chart map. The original finite cover separates algebra elements, so
these local equalities prove equality of complete bounded maps.

`domainInChartSelfIso` and `domainInChartTransIso` package self and transitive
comparisons with bounded identity maps on the unchanged original domain
algebra. Their structural triangles use the proved bounded-map equalities,
and existing full-domain arrow uniqueness proves the inverse equations.

The proof uses only actual finite full-domain covers, original-chart
localization and extension, their original identity-restriction comparison,
the constructed all-test local formula and source naturality. No new
original-literature assertion, analytic output or algebra-map equality inferred
from spectrum-point functions is used. Arbitrary positive radii, trivial
valuations, nonreduced or zero quotients and permitted empty covers are retained.
General local-domain restriction categories, the extended atlas and its net,
analytic or equivariant sites, and the Harris tower remain further work.
