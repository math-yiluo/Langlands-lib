# Unique gluing of arbitrary quotient-domain matching families

Author: Worker 36.

This internal construction glues arbitrary matching arrows of the actual source
quotient on any original-domain quasinet cover. It uses the proved full strong
refinement of these matching arrows, the constructed quotient glue for literal
full strong matching families, and quotient separation on actual domain covers.
No new original-literature assertion is introduced.

The input `QuotientDomainMatchingFamily` contains quotient arrows on the given
domains and their equations on intersections. Its constructed `strongRefinement`
provides complete strong maps on an actual refining family of ambient chart
domains and a proof that this family is still a quasinet cover. The definition
`glue` applies the existing literal strong-family gluing construction to those
maps. This constructs an arrow in the actual source quotient without assuming a
global strong representative for any input arrow or for the glue.

`glue_refinement` records the previously proved recovery equation on each refined
ambient domain. To prove `glue_restrict` on an original member, use quotient
separation on its selected original-chart cover. For each selected chart,
precompose the comparison with the actual nested-domain isomorphism. Its
inclusion triangle and the ambient domain inclusion triangle turn the left side
into the restriction of the global glue to the refined ambient domain. The
refined recovery equation identifies this with the quotient image of the
complete transported strong map; the proved local representation equation
identifies the right side with the same image. Cancellation of the isomorphism
and separation on the selected cover give the original local arrow.

`glue_unique` applies quotient separation to the original input cover. Thus
`existsUnique_glue` proves existence and uniqueness among all quotient arrows,
including arrows not supplied with global strong representatives. All bounded
map information is preserved by the full strong refinement and quotient-arrow
equalities; no equality principle using only spectrum points is invoked.

The coefficient field is complete and ultrametric and may be trivially valued.
Field, space, chart-index and cover-index universes are independent. Empty
domains are allowed. Relative-domain and arbitrary-covering-sieve sheaf gluing,
full analytic identification, and the etale and equivariant constructions remain
subsequent obligations.
