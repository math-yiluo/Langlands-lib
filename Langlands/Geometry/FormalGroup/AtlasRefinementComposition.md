# Composition of principal-cover refinements

`CoverRefinement.comp` composes actual localization containments. Its atlas
is compared with the atlas obtained by successive restriction by the actual
formal isomorphism `compIso`. Evaluating that formal isomorphism identifies
direct restriction with successive restriction of every full compatible family.

## Provenance and scope

This is derived infrastructure for Drinfeld's localization-gluing convention:
Drinfeld, *Coverings of p-adic symmetric regions* (1976), printed p.109,
paragraph immediately before section 2 (PDF page 3). The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
That paragraph admits formal groups glued from formal groups over localizations.
The composition and comparison constructions here are derived from the
implemented localization maps, chart laws and formal transitions, rather than
attributed as a separate theorem to that paragraph.

O and R are arbitrary commutative rings with an O-algebra structure on R.
The coordinate type is finite and lies in `Type`. Tests are R-algebras in R's
universe v, and the full-family point modules lie in v+1. Covers can be infinite
and chart laws can vary. The finer-cover containments are actual localization
unit conditions. No point equivalence or formal comparison is supplied as input.

This module supplies reflexive refinement data and one comparison for two
successive refinements. It does not prove unit or associativity coherence laws,
compare arbitrary source selections, establish transitivity of arbitrary
`Comparison` witnesses, construct a quotient of presentations, or construct
framing, heights, moduli or representing objects.

## Actual composite containments and coefficients

`refl X` uses X's own cover, selects each chart itself, and uses the fact that
its generator is a unit in its principal localization.

For `q : CoverRefinement X` and `r : CoverRefinement q.atlas`, `q.comp r` has
r's final cover and selects `q.source (r.source b)` in X. The first containment
makes this original generator a unit on the intermediate chart. Applying
`q.source_unit` over the final localization, with r's containment, proves the
composite containment.

`comp_coefficient` identifies the actual O-algebra map from the selected
original localization to the final localization with the composite of the two
coefficient maps. Localization extensionality reduces this equality to elements
of R. Each route sends such an element to its image under the algebra map,
by the proved `chartCoefficient_algebraMap` equations.

## Formal comparison of direct and successive restriction

`compChartIso` compares both final chart laws with the same original chart law.
The direct chart comparison is followed by the inverse of the composite of the
two successive chart comparisons. These are actual formal O-module
isomorphisms. `compChartIso_hom_coordinates` and
`compChartIso_inv_coordinates` prove that both directions have identity
coordinate series, using the identity laws for formal substitution.

`successive_transition_coordinates` applies the two refinement transition
identities to recover the original transition at the composite source charts.
`comp_transition_coordinates` then identifies the direct and successive
transition coordinates.

`compHom` and `compInv` assemble the two chart maps into formal atlas maps on
the common final cover. Coefficient naturality follows from their identity
coordinate series. Their transition squares follow from
`comp_transition_coordinates` after identity substitution. `compIso` uses the
two formal inverse equations of `compChartIso`, checked in every test and chart,
to give both formal inverse equations of the atlas maps.

## Full-family compatibility

For every R-algebra A and full compatible X-family x, `comp_onPoints` proves
that applying `compIso.hom.onPoints` to direct restriction of x equals first
restricting x along q and then along r. Extensionality reduces this equality to
every chart test, including its arbitrary structure map from A. Both restricted
components are the same original-family component at the composite source
chart. Evaluating the identity-coordinate comparison fixes that component.
The maps preserve the formal group addition and O-action through their actual
formal homomorphism structures; no coordinatewise addition is imposed.
