# Quotient morphism gluing on relative original-domain covers

Author: Worker 36.

This internal construction extends the proved unique gluing of arbitrary
quotient-domain matching arrows from a cover of the whole presentation to a
relative quasinet cover of any fixed original-chart domain. Its ingredients are
the constructed original-domain subspaces, their image-only quotient
factorization and monic inclusions, the existing comparison to a nested
subspace domain, and the previously constructed global quotient glue. It makes
no new original-literature assertion.

For ambient domains `T ≤ S`, `relativeDomainComparison` already maps the actual
nested realization of `T` inside `S` to its ambient realization. The new
`relativeDomainComparison_inclusion` is its full ambient inclusion triangle.
`relativeDomainInverse` factors the actual arrow `domainMap hTS` through the
nested domain. The factorization's image condition follows from the proved
underlying value formula for that arrow. Its inclusion triangle is
`relativeDomainInverse_inclusion`. Cancelling the proved monic domain
inclusions shows that the two composites are identities; `relativeDomainIso`
therefore constructs an isomorphism of actual quotient objects, not merely a
bijection of their spaces. `relativeDomainComparison_naturality` proves the
comparison square for every inclusion between ambient domains contained in
`S`, again by cancelling the actual ambient monic inclusion and using the
inclusion triangles.

Given `QuotientDomainMatchingFamily A B D` and containments `D k ≤ S`,
`onSubspace` precomposes each arbitrary local quotient arrow with this
comparison. The intersection of the restricted subspace domains is the
restriction of their ambient intersection. The two naturality squares turn its
local overlap equation into the original quotient overlap equation, precomposed
with the intersection comparison. This proves matching of complete quotient
arrows; it does not use an equality principle based only on spectrum points.

`relativeDomainCover_subspace` already transfers the full finite relative
neighborhood witnesses of a cover of `S` to a cover of its actual subspace
presentation. `glueRelative` applies the proved whole-presentation gluing to
`onSubspace` and that transferred cover. For `glueRelative_restrict`, precompose
with the comparison isomorphism of one member. Its triangle and the proved
whole-presentation recovery equation give equality; cancellation of this
isomorphism recovers the original ambient local arrow. The proof applies to
arbitrary quotient arrows without requiring global strong representatives.

`glueRelative_unique` uses the existing quotient separation theorem for relative
domain covers. `existsUnique_glueRelative` packages the constructed arrow, all
its restriction equations and uniqueness among all quotient arrows. The field,
ambient-space, chart-index and cover-index universes remain independent. The
field is complete and ultrametric; trivial valuations and empty domains are
allowed. Sheafness on arbitrary covering sieves, full analytic identification,
and the etale and equivariant sites remain subsequent obligations.
