# Actual coefficient-extension comparisons for global order covers

This module constructs actual full-order formal comparisons between
coefficient extension of a global formal module restricted to a principal
cover and restriction of its extended global module to the image cover.
The construction uses the existing localization coefficient lifts and chart
isomorphisms; it makes no new literature assertion.

`OrderAction.mapCompIso` lifts the existing identity-coordinate global formal
module composition isomorphism to the complete acting order. Forward order
commutation follows by composing the actual coefficient maps; the existing
`ofModuleIso` construction proves inverse commutation by the actual inverse
equations.

`globalCoverBaseChartIso` compares the two test-chart formal modules. It first
uses the extended chart's actual comparison with its selected original chart,
then the original global chart comparison, then the inverse global coefficient
composition isomorphism, and finally the inverse extended-global chart
comparison. Every map is an actual formal isomorphism with identity coordinate
series. The two coordinate equations record that for both directions.

The original global transitions and their coefficient extensions also have
identity coordinate series. Consequently these actual chart maps are natural
in every coefficient test and commute with the actual atlas transitions.
`globalCoverBaseHom` and `globalCoverBaseInv` retain the full acting order, and
`globalCoverBaseIso` packages their actual chartwise inverse equations. Equality
of point evaluations is not used to infer equality of formal maps.

The parameters are commutative coefficient rings `O`, `R`, a ring `D` acting
linearly over `O`, a finite coordinate type, an actual global formal module and
order action, a principal cover of `R` and any commutative `R`-algebra `S`.
Coefficient rings and tests share universe `v`; `O` and `D` may have separate
universes. Covers need not be finite, and coefficient maps may merge original
generators. The source retains the original atlas's actual selected source
charts. Supplied-target scalar transport and the fixed-frame comparison for
varying Nilp bases are further constructions.
