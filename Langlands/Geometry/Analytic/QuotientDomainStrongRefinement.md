# Full strong refinement of arbitrary quotient-domain matching families

Author: Worker 36.

This internal construction turns arbitrary matching arrows in the actual source
quotient into a literal matching family of full strong maps on a constructed
refinement of the original domains. It uses the proved chart representations,
full nested-domain transport, quotient-domain composition, faithful embedding
of full strong maps, and finite relative local refinement of original chart
families. It introduces no original-literature assertion.

`QuotientDomainMatchingFamily` takes actual quotient arrows on original domains
and their equality after restriction to each intersection. It assumes neither
strong representatives nor a global arrow. Its `restrict_eq` follows by further
restricting the intersection equation to any smaller common domain, using
composition of actual quotient domain maps.

For each member, `chartData` chooses its already constructed whole-chart strong
representation. `RefinementIndex` retains the member and one of its selected
original charts. `refinementDomain` is the ambient image of that chart domain
inside the member. Its carrier is exactly the range of the same original ambient
chart; it is contained in the original member. `refinementMap` transports the
complete local strong map from the nested presentation to this ambient-image
presentation. All original chart algebras and every admissible bounded pullback
are retained.

`refinementMap_represents` identifies this full map's quotient image with the
input arrow restricted to the refined domain. The nested-domain inclusion
triangle, the original chart representation equation, and the full transport
comparison with quotient composition prove this equality.

On the intersection of two refined domains, their quotient images agree:
compose their representation equations with the two intersection inclusions,
and apply `restrict_eq` on that common subdomain of the two original members.
The proved injectivity of the full strong-map functor then proves equality of
the complete directly restricted strong maps, including bounded algebra maps
that spectrum points alone may not detect. These maps and equations define
`strongRefinement`. No new faithfulness hypothesis or compatibility choice is
introduced.

`refinementDomain_locallyRefines` uses the finite relative neighborhood
refinement supplied by the selected-chart families in each original member.
The existing assembled selection predicate indexes the same ambient original
charts; retaining their member labels only enlarges the indexed refining
family. Thus all finite relative neighborhood witnesses survive. Composing
with any given quasinet cover proves `strongRefinement_cover`. Separately,
`chartData_cover` records that the selected whole-chart family covers each
member in its own actual subspace topology.

The coefficient field is complete and ultrametric, with trivial valuations
allowed. Field, space, chart-index and covering-index universes remain
independent. Empty domains are allowed. This unit constructs the full strong
refinement; existence and recovery of a global quotient glue, full analytic
identification, and etale and equivariant sites remain separate obligations.
