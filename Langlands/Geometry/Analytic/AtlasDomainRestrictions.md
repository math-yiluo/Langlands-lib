# Actual bounded restrictions between arbitrary local full affinoid domains

Work with an arbitrary indexed affinoid atlas over a complete ultrametric normed
field. A source full domain `U` in original chart `i` and a target full domain
`V` in original chart `j` need only have ambient images related by containment.
Neither a common upper chart, directedness nor a greatest chart is assumed.

`domainInChartInclusionOfSubset` reexpresses `U` in chart `j` by the constructed
full `domainInChart`, then uses actual full-domain representation to construct
its inclusion into `V`. `domainRestriction` is precisely this inclusion's
bounded algebra map from `V.algebra` to the unchanged `U.algebra`.
`domainRestriction_comp_baseMap` retains its exact structural equation.
`eq_domainRestriction_of_over_base` derives uniqueness of the complete bounded
map from that equation using the original full representation of `V`.

`domainRestriction_chart` proves the ambient spectrum chart equation by
evaluating the exact structural equation and using the constructed source
chart equation. It does not infer equality of algebra maps from spectrum points.

`domainRestriction_comp_chart` considers any original chart containing the
target domain's ambient image. Source naturality of the reexpressed inclusion
and the proved reexpression coherence identify its composite with the source's
direct bounded structural map from that chart.
For three local domains in independently chosen original charts,
`domainRestriction_comp` applies this result to the target's original chart.
The two structural equations then coincide, so original full-domain uniqueness
identifies the complete composite with the direct restriction.

`domainRestriction_sameChart` recovers every original actual full-domain
inclusion, and `domainRestriction_id` recovers the bounded identity.
`domainRestriction_represents` proves full representation of the literal
relative ambient subset in the target domain's spectrum. It is the existing
relative full-domain representation of the constructed inclusion. Injectivity
of the target domain spectrum map identifies its locus with the literal
preimage of the source's ambient image.

This is an internal derivation from actual full-domain reexpression,
its bounded-map naturality and coherence, original representation uniqueness
and actual relative full domains. No new original-literature assertion, assumed
analytic restriction output or peer draft is used. The original algebras,
including nilpotents, zero quotients and arbitrary positive radii, are retained;
trivial valuations and empty covers remain allowed. The local-domain category,
the extended analytic atlas and its net, analytic or equivariant sites and
the Harris tower remain further work.
